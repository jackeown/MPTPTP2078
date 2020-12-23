%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1802+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:28 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  220 (1202 expanded)
%              Number of clauses        :  130 ( 258 expanded)
%              Number of leaves         :   24 ( 423 expanded)
%              Depth                    :   25
%              Number of atoms          : 1126 (9512 expanded)
%              Number of equality atoms :  198 ( 349 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),sK5)
        & m1_subset_1(sK5,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tmap_1(sK4,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK4),X3)
            & m1_subset_1(X3,u1_struct_0(sK4)) )
        & r1_tsep_1(X1,sK4)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_tsep_1(sK3,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
                & r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & r1_tsep_1(sK3,sK4)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f45,f59,f58,f57,f56])).

fof(f100,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,(
    ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f99,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f102,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f60])).

fof(f94,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f96,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f104,plain,(
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
    inference(equality_resolution,[],[f61])).

fof(f105,plain,(
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
    inference(equality_resolution,[],[f104])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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

fof(f76,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f101,plain,(
    r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
                    & u1_struct_0(X1) = sK1(X0,X1,X2)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f51,f52])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,plain,
    ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_31,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ r1_xboole_0(u1_struct_0(X0),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_33,negated_conjecture,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_474,plain,
    ( ~ r1_xboole_0(u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(X2,k6_tmap_1(X2,X1),k7_tmap_1(X2,X1),X0) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X2,X1) != k8_tmap_1(sK2,sK3)
    | sK5 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_33])).

cnf(c_475,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_pre_topc(sK4,X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_479,plain,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_37,c_34])).

cnf(c_480,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(sK4,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_479])).

cnf(c_1593,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
    | sK2 != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_480])).

cnf(c_1594,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1593])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1598,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1594,c_42,c_41,c_40])).

cnf(c_1599,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_1598])).

cnf(c_1744,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X2),k7_tmap_1(sK2,X2),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X2) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X1) != X2
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_1599])).

cnf(c_1745,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(X1)),k7_tmap_1(sK2,u1_struct_0(X1)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(X1)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1744])).

cnf(c_8487,plain,
    ( ~ r1_tsep_1(X0_57,X1_57)
    | ~ m1_subset_1(u1_struct_0(X1_57),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(X1_57)),k7_tmap_1(sK2,u1_struct_0(X1_57)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(X1_57)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X0_57) != u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_1745])).

cnf(c_10938,plain,
    ( ~ r1_tsep_1(X0_57,sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(sK3)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X0_57) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8487])).

cnf(c_13579,plain,
    ( ~ r1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK4)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_10938])).

cnf(c_3,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_32,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_276,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_32,c_26,c_25,c_13])).

cnf(c_277,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_276])).

cnf(c_38,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1342,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_277,c_38])).

cnf(c_1343,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1342])).

cnf(c_1345,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1343,c_42,c_41,c_40])).

cnf(c_8497,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_1345])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_40])).

cnf(c_3467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_3466])).

cnf(c_3471,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3467,c_42,c_41])).

cnf(c_8446,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56))))) ),
    inference(subtyping,[status(esa)],[c_3471])).

cnf(c_10091,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8446])).

cnf(c_11603,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8497,c_10091])).

cnf(c_11,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2994,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_40])).

cnf(c_2995,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_2994])).

cnf(c_2999,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2995,c_42,c_41])).

cnf(c_8471,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_56),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56)))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_2999])).

cnf(c_10066,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_56),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_56))) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8471])).

cnf(c_11588,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8497,c_10066])).

cnf(c_8518,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_11386,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_8518])).

cnf(c_8541,plain,
    ( k2_tmap_1(X0_57,X1_57,X0_56,X2_57) = k2_tmap_1(X3_57,X4_57,X1_56,X5_57)
    | X0_57 != X3_57
    | X1_57 != X4_57
    | X2_57 != X5_57
    | X0_56 != X1_56 ),
    theory(equality)).

cnf(c_11190,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK4) = k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK2 != sK2
    | sK4 != sK4
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_8541])).

cnf(c_8517,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_11029,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8517])).

cnf(c_35,negated_conjecture,
    ( r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_8512,negated_conjecture,
    ( r1_tsep_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_10031,plain,
    ( r1_tsep_1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8512])).

cnf(c_30,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_8514,plain,
    ( ~ r1_tsep_1(X0_57,X1_57)
    | r1_tsep_1(X1_57,X0_57)
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_10029,plain,
    ( r1_tsep_1(X0_57,X1_57) != iProver_top
    | r1_tsep_1(X1_57,X0_57) = iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | l1_struct_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8514])).

cnf(c_10882,plain,
    ( r1_tsep_1(sK4,sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10031,c_10029])).

cnf(c_10883,plain,
    ( r1_tsep_1(sK4,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10882])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_40])).

cnf(c_3449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_3448])).

cnf(c_3453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3449,c_42,c_41])).

cnf(c_8447,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0_56)) ),
    inference(subtyping,[status(esa)],[c_3453])).

cnf(c_10818,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_8447])).

cnf(c_10819,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10818])).

cnf(c_21,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1363,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(k8_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_1364,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1363])).

cnf(c_1366,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1364,c_42,c_41,c_40])).

cnf(c_4128,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | k8_tmap_1(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1366])).

cnf(c_4129,plain,
    ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ l1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_4128])).

cnf(c_19,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1420,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_38])).

cnf(c_1421,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1420])).

cnf(c_1423,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1421,c_42,c_41,c_40])).

cnf(c_3369,plain,
    ( l1_struct_0(X0)
    | k8_tmap_1(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1423])).

cnf(c_3370,plain,
    ( l1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_3369])).

cnf(c_4131,plain,
    ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4129,c_3370])).

cnf(c_29,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1385,plain,
    ( v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_38])).

cnf(c_1386,plain,
    ( v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1385])).

cnf(c_1388,plain,
    ( v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1386,c_42,c_41,c_40])).

cnf(c_1350,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_38])).

cnf(c_1351,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1350])).

cnf(c_1353,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1351,c_40])).

cnf(c_7,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_17,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_16,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_266,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_17,c_16])).

cnf(c_1106,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_266,c_38])).

cnf(c_1107,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1106])).

cnf(c_1109,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1107,c_42,c_41,c_40])).

cnf(c_1110,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_1109])).

cnf(c_1360,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1353,c_1110])).

cnf(c_1395,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1388,c_1360])).

cnf(c_1873,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != X3
    | k9_tmap_1(sK2,sK3) != X0
    | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) != X5
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != X2
    | u1_struct_0(sK2) != X4
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1395])).

cnf(c_1874,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1873])).

cnf(c_1123,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_38])).

cnf(c_1124,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1123])).

cnf(c_1134,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_38])).

cnf(c_1135,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1134])).

cnf(c_1876,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1874,c_42,c_41,c_40,c_1124,c_1135,c_1386])).

cnf(c_1877,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_1876])).

cnf(c_4232,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4131,c_1877])).

cnf(c_8422,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_4232])).

cnf(c_10115,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) = iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8422])).

cnf(c_10535,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10115,c_8497])).

cnf(c_8563,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_8518])).

cnf(c_4130,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | l1_struct_0(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4129])).

cnf(c_3371,plain,
    ( l1_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3370])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1374,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_38])).

cnf(c_1375,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1374])).

cnf(c_1377,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1375,c_40])).

cnf(c_3299,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1377])).

cnf(c_3300,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_3299])).

cnf(c_1231,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_36])).

cnf(c_1232,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1231])).

cnf(c_1234,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1232,c_40])).

cnf(c_3108,plain,
    ( l1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1234])).

cnf(c_3109,plain,
    ( l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_3108])).

cnf(c_1352,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_45,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13579,c_11603,c_11588,c_11386,c_11190,c_11029,c_10883,c_10819,c_10535,c_8497,c_8563,c_4130,c_3371,c_3300,c_3109,c_1352,c_1351,c_45,c_40])).


%------------------------------------------------------------------------------
