%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:06 EST 2020

% Result     : Theorem 23.31s
% Output     : CNFRefutation 23.31s
% Verified   : 
% Statistics : Number of formulae       :  320 (12086 expanded)
%              Number of clauses        :  224 (2560 expanded)
%              Number of leaves         :   22 (4383 expanded)
%              Depth                    :   36
%              Number of atoms          : 1542 (96939 expanded)
%              Number of equality atoms :  494 (3968 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),sK5)
        & m1_subset_1(sK5,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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

fof(f63,plain,(
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

fof(f62,plain,
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

fof(f66,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f52,f65,f64,f63,f62])).

fof(f106,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f104,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f102,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f103,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f112,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f113,plain,(
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
    inference(equality_resolution,[],[f112])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f98,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f105,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f108,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f107,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f114,plain,(
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
    inference(equality_resolution,[],[f77])).

fof(f115,plain,(
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
    inference(equality_resolution,[],[f114])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f111,plain,(
    ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f66])).

fof(f110,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f66])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f69,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f109,plain,(
    r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_33,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_40,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1363,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_40])).

cnf(c_1364,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1363])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1366,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1364,c_42])).

cnf(c_15753,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_1366])).

cnf(c_17892,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15753])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_4486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_44])).

cnf(c_4487,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_4486])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_4491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4487,c_43,c_42])).

cnf(c_15693,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_tmap_1(sK2,X0_59) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_4491])).

cnf(c_17951,plain,
    ( k7_tmap_1(sK2,X0_59) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15693])).

cnf(c_19906,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_17892,c_17951])).

cnf(c_9,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_294,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_33,c_24,c_23,c_22])).

cnf(c_295,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_1347,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_295,c_40])).

cnf(c_1348,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1347])).

cnf(c_1350,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1348,c_44,c_43,c_42])).

cnf(c_15755,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_1350])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_44])).

cnf(c_4415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_4414])).

cnf(c_4419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4415,c_43,c_42])).

cnf(c_15697,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_59))))) ),
    inference(subtyping,[status(esa)],[c_4419])).

cnf(c_17947,plain,
    ( m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_59))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15697])).

cnf(c_20607,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15755,c_17947])).

cnf(c_32,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1374,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_40])).

cnf(c_1375,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1374])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1377,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1375,c_44,c_43,c_42,c_41])).

cnf(c_15752,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1377])).

cnf(c_20608,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20607,c_15752,c_19906])).

cnf(c_47,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_1365,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1364])).

cnf(c_20615,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20608,c_47,c_1365])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_38,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1872,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0
    | sK2 != X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_38])).

cnf(c_1873,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK4,X0) = u1_struct_0(sK4)
    | k9_tmap_1(sK2,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_1872])).

cnf(c_1877,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ v1_funct_1(X0)
    | sK1(sK2,sK4,X0) = u1_struct_0(sK4)
    | k9_tmap_1(sK2,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1873,c_44,c_43,c_42])).

cnf(c_1878,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_1(X0)
    | sK1(sK2,sK4,X0) = u1_struct_0(sK4)
    | k9_tmap_1(sK2,sK4) = X0 ),
    inference(renaming,[status(thm)],[c_1877])).

cnf(c_15737,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_1(X0_59)
    | sK1(sK2,sK4,X0_59) = u1_struct_0(sK4)
    | k9_tmap_1(sK2,sK4) = X0_59 ),
    inference(subtyping,[status(esa)],[c_1878])).

cnf(c_17907,plain,
    ( sK1(sK2,sK4,X0_59) = u1_struct_0(sK4)
    | k9_tmap_1(sK2,sK4) = X0_59
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15737])).

cnf(c_1230,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_38])).

cnf(c_1231,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK4)) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1230])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1233,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK4)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1231,c_44,c_43,c_42,c_39])).

cnf(c_15763,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK4)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1233])).

cnf(c_18015,plain,
    ( sK1(sK2,sK4,X0_59) = u1_struct_0(sK4)
    | k9_tmap_1(sK2,sK4) = X0_59
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17907,c_15763])).

cnf(c_21552,plain,
    ( sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK4)
    | k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20615,c_18015])).

cnf(c_20,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5119,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_44])).

cnf(c_5120,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_5119])).

cnf(c_5124,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5120,c_43,c_42])).

cnf(c_15660,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_59),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_59)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_5124])).

cnf(c_17981,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_59),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_59))) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15660])).

cnf(c_20066,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15755,c_17981])).

cnf(c_20067,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20066,c_15752,c_19906])).

cnf(c_1219,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_38])).

cnf(c_1220,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1219])).

cnf(c_1222,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1220,c_42])).

cnf(c_15764,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_1222])).

cnf(c_17884,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15764])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_44])).

cnf(c_4397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v1_funct_1(k7_tmap_1(sK2,X0))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_4396])).

cnf(c_4401,plain,
    ( v1_funct_1(k7_tmap_1(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4397,c_43,c_42])).

cnf(c_4402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_4401])).

cnf(c_15698,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0_59)) ),
    inference(subtyping,[status(esa)],[c_4402])).

cnf(c_17946,plain,
    ( m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,X0_59)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15698])).

cnf(c_19498,plain,
    ( v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17884,c_17946])).

cnf(c_19905,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_17884,c_17951])).

cnf(c_22870,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19498,c_19905])).

cnf(c_25756,plain,
    ( sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK4)
    | k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21552,c_47,c_1365,c_20067,c_22870])).

cnf(c_4,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_10,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1644,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_38])).

cnf(c_1645,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK4,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_1644])).

cnf(c_1649,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK4,X0)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1645,c_44,c_43,c_42])).

cnf(c_1650,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK4,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK4) = X0 ),
    inference(renaming,[status(thm)],[c_1649])).

cnf(c_5452,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ v1_funct_2(X6,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X6)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X6 != X3
    | k9_tmap_1(sK2,sK4) = X6
    | k7_tmap_1(sK2,sK1(sK2,sK4,X6)) != X3
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X6))) != X2
    | u1_struct_0(k8_tmap_1(sK2,sK4)) != X5
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_1650])).

cnf(c_5453,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1))))
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK4)))
    | k9_tmap_1(sK2,sK4) = X1
    | k7_tmap_1(sK2,sK1(sK2,sK4,X1)) != X1 ),
    inference(unflattening,[status(thm)],[c_5452])).

cnf(c_15732,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1_59))))
    | ~ v1_funct_2(X1_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1_59))))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(X1_59)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1_59))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK4)))
    | k9_tmap_1(sK2,sK4) = X1_59
    | k7_tmap_1(sK2,sK1(sK2,sK4,X1_59)) != X1_59 ),
    inference(subtyping,[status(esa)],[c_5453])).

cnf(c_17912,plain,
    ( k9_tmap_1(sK2,sK4) = X0_59
    | k7_tmap_1(sK2,sK1(sK2,sK4,X0_59)) != X0_59
    | v1_funct_2(X1_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15732])).

cnf(c_18045,plain,
    ( k9_tmap_1(sK2,sK4) = X0_59
    | k7_tmap_1(sK2,sK1(sK2,sK4,X0_59)) != X0_59
    | v1_funct_2(X1_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17912,c_15763])).

cnf(c_45,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_148,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_150,plain,
    ( v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_152,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_154,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_22572,plain,
    ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))))) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(X1_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) != iProver_top
    | k7_tmap_1(sK2,sK1(sK2,sK4,X0_59)) != X0_59
    | k9_tmap_1(sK2,sK4) = X0_59 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18045,c_45,c_47,c_150,c_154])).

cnf(c_22573,plain,
    ( k9_tmap_1(sK2,sK4) = X0_59
    | k7_tmap_1(sK2,sK1(sK2,sK4,X0_59)) != X0_59
    | v1_funct_2(X1_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_22572])).

cnf(c_25758,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | k7_tmap_1(sK2,u1_struct_0(sK4)) != k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_25756,c_22573])).

cnf(c_25759,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | k6_partfun1(u1_struct_0(sK2)) != k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25758,c_19905])).

cnf(c_25760,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_25759])).

cnf(c_87378,plain,
    ( v1_funct_1(X0_59) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25760,c_47,c_1365,c_20067,c_20608,c_22870])).

cnf(c_87379,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_87378])).

cnf(c_87394,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK4)))))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_25756,c_87379])).

cnf(c_1203,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_295,c_38])).

cnf(c_1204,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK4)) = k8_tmap_1(sK2,sK4) ),
    inference(unflattening,[status(thm)],[c_1203])).

cnf(c_1206,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK4)) = k8_tmap_1(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1204,c_44,c_43,c_42])).

cnf(c_15766,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK4)) = k8_tmap_1(sK2,sK4) ),
    inference(subtyping,[status(esa)],[c_1206])).

cnf(c_87395,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_87394,c_15763,c_15766])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1845,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X2) = X0
    | sK2 != X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_38])).

cnf(c_1846,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | m1_subset_1(sK1(sK2,sK4,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_1845])).

cnf(c_1850,plain,
    ( m1_subset_1(sK1(sK2,sK4,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1846,c_44,c_43,c_42])).

cnf(c_1851,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | m1_subset_1(sK1(sK2,sK4,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK4) = X0 ),
    inference(renaming,[status(thm)],[c_1850])).

cnf(c_15738,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | m1_subset_1(sK1(sK2,sK4,X0_59),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0_59)
    | k9_tmap_1(sK2,sK4) = X0_59 ),
    inference(subtyping,[status(esa)],[c_1851])).

cnf(c_17906,plain,
    ( k9_tmap_1(sK2,sK4) = X0_59
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))))) != iProver_top
    | m1_subset_1(sK1(sK2,sK4,X0_59),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15738])).

cnf(c_18018,plain,
    ( k9_tmap_1(sK2,sK4) = X0_59
    | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK1(sK2,sK4,X0_59),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17906,c_15763])).

cnf(c_22006,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20615,c_18018])).

cnf(c_28805,plain,
    ( m1_subset_1(sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22006,c_47,c_1365,c_20067,c_22870])).

cnf(c_28806,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_28805])).

cnf(c_28811,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_28806,c_17951])).

cnf(c_29126,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top
    | m1_subset_1(sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28811,c_17981])).

cnf(c_29580,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top
    | k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29126,c_47,c_1365,c_20067,c_22006,c_22870])).

cnf(c_29581,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_29580])).

cnf(c_29125,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_28811,c_17947])).

cnf(c_31443,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29125,c_47,c_1365,c_20067,c_22006,c_22870])).

cnf(c_87385,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_31443,c_87379])).

cnf(c_87409,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_87395,c_22870,c_29581,c_87385])).

cnf(c_87421,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_25756,c_87409])).

cnf(c_87422,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_87421,c_15763,c_15766])).

cnf(c_87513,plain,
    ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_87422,c_45,c_47,c_150,c_154])).

cnf(c_25,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1720,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_40])).

cnf(c_1721,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1720])).

cnf(c_1723,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1721,c_44,c_43,c_42])).

cnf(c_15740,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
    inference(subtyping,[status(esa)],[c_1723])).

cnf(c_17904,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15740])).

cnf(c_18013,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17904,c_15752])).

cnf(c_21550,plain,
    ( sK1(sK2,sK4,k9_tmap_1(sK2,sK3)) = u1_struct_0(sK4)
    | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18013,c_18015])).

cnf(c_46,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1382,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_40])).

cnf(c_1383,plain,
    ( ~ v2_pre_topc(sK2)
    | v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1382])).

cnf(c_1384,plain,
    ( v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1383])).

cnf(c_26,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1709,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_40])).

cnf(c_1710,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1709])).

cnf(c_1712,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1710,c_44,c_43,c_42])).

cnf(c_15741,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
    inference(subtyping,[status(esa)],[c_1712])).

cnf(c_17903,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15741])).

cnf(c_18010,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17903,c_15752])).

cnf(c_25512,plain,
    ( sK1(sK2,sK4,k9_tmap_1(sK2,sK3)) = u1_struct_0(sK4)
    | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21550,c_45,c_46,c_47,c_1384,c_18010])).

cnf(c_13,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_284,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_26,c_25])).

cnf(c_1698,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_284,c_40])).

cnf(c_1699,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1698])).

cnf(c_1701,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1699,c_44,c_43,c_42,c_1364,c_1383])).

cnf(c_5870,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) != X0
    | k9_tmap_1(sK2,sK4) = X0
    | k7_tmap_1(sK2,sK1(sK2,sK4,X0)) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_1650,c_1701])).

cnf(c_5871,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_5870])).

cnf(c_2607,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) != X0
    | k9_tmap_1(sK2,sK4) = X0
    | k7_tmap_1(sK2,sK1(sK2,sK4,X0)) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_1650,c_1701])).

cnf(c_2608,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_2607])).

cnf(c_2610,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2608,c_44,c_43,c_42,c_1383])).

cnf(c_2611,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
    inference(renaming,[status(thm)],[c_2610])).

cnf(c_5873,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5871,c_44,c_43,c_42,c_1383,c_2608])).

cnf(c_5874,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
    inference(renaming,[status(thm)],[c_5873])).

cnf(c_15729,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
    | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
    inference(subtyping,[status(esa)],[c_5874])).

cnf(c_17915,plain,
    ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4))
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15729])).

cnf(c_18023,plain,
    ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17915,c_15752,c_15755,c_15763])).

cnf(c_18024,plain,
    ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18023])).

cnf(c_23556,plain,
    ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18024,c_18010,c_18013])).

cnf(c_23558,plain,
    ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_23556,c_19906])).

cnf(c_25514,plain,
    ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK4))) != u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_25512,c_23558])).

cnf(c_25517,plain,
    ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_25514,c_15763,c_15766])).

cnf(c_25518,plain,
    ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_25517])).

cnf(c_25522,plain,
    ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,u1_struct_0(sK4)) != k6_partfun1(u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_25512,c_25518])).

cnf(c_25523,plain,
    ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
    | k6_partfun1(u1_struct_0(sK2)) != k6_partfun1(u1_struct_0(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_25522,c_19905])).

cnf(c_25524,plain,
    ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_25523])).

cnf(c_30,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_35,negated_conjecture,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ r1_xboole_0(u1_struct_0(X3),X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),X3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
    | sK5 != X2
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_35])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_pre_topc(sK4,X1)
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_524,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_39,c_36])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(sK4,X1)
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_524])).

cnf(c_1980,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
    | sK2 != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_525])).

cnf(c_1981,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1980])).

cnf(c_1985,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1981,c_44,c_43,c_42])).

cnf(c_1986,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_1985])).

cnf(c_15733,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(u1_struct_0(sK4),X0_59)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0_59),k7_tmap_1(sK2,X0_59),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0_59) != k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_1986])).

cnf(c_17911,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,X0_59),k7_tmap_1(sK2,X0_59),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0_59) != k8_tmap_1(sK2,sK3)
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(u1_struct_0(sK4),X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15733])).

cnf(c_83964,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,X0_59),k7_tmap_1(sK2,X0_59),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK4),sK4)
    | k6_tmap_1(sK2,X0_59) != k8_tmap_1(sK2,sK3)
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(u1_struct_0(sK4),X0_59) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25524,c_17911])).

cnf(c_87525,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,X0_59),k7_tmap_1(sK2,X0_59),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK4)
    | k6_tmap_1(sK2,X0_59) != k8_tmap_1(sK2,sK3)
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(u1_struct_0(sK4),X0_59) != iProver_top ),
    inference(demodulation,[status(thm)],[c_87513,c_83964])).

cnf(c_88347,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k6_partfun1(u1_struct_0(sK2)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK4)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19906,c_87525])).

cnf(c_88396,plain,
    ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK4)
    | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_88347,c_15755])).

cnf(c_88397,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_88396])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1480,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_40])).

cnf(c_1481,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1480])).

cnf(c_1483,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1481,c_42])).

cnf(c_10241,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_1483])).

cnf(c_10242,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_10241])).

cnf(c_1336,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_38])).

cnf(c_1337,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1336])).

cnf(c_1339,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1337,c_42])).

cnf(c_9784,plain,
    ( l1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_1339])).

cnf(c_9785,plain,
    ( l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_9784])).

cnf(c_15,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_37,negated_conjecture,
    ( r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_565,plain,
    ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_37])).

cnf(c_566,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_12258,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_struct_0(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_9785,c_566])).

cnf(c_12329,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10242,c_12258])).

cnf(c_15636,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_12329])).

cnf(c_18007,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15636])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_15771,plain,
    ( ~ r1_xboole_0(X0_59,X1_59)
    | r1_xboole_0(X1_59,X0_59) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_17879,plain,
    ( r1_xboole_0(X0_59,X1_59) != iProver_top
    | r1_xboole_0(X1_59,X0_59) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15771])).

cnf(c_19056,plain,
    ( r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18007,c_17879])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_88397,c_19056,c_1365,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:16:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 23.31/3.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.31/3.54  
% 23.31/3.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.31/3.54  
% 23.31/3.54  ------  iProver source info
% 23.31/3.54  
% 23.31/3.54  git: date: 2020-06-30 10:37:57 +0100
% 23.31/3.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.31/3.54  git: non_committed_changes: false
% 23.31/3.54  git: last_make_outside_of_git: false
% 23.31/3.54  
% 23.31/3.54  ------ 
% 23.31/3.54  
% 23.31/3.54  ------ Input Options
% 23.31/3.54  
% 23.31/3.54  --out_options                           all
% 23.31/3.54  --tptp_safe_out                         true
% 23.31/3.54  --problem_path                          ""
% 23.31/3.54  --include_path                          ""
% 23.31/3.54  --clausifier                            res/vclausify_rel
% 23.31/3.54  --clausifier_options                    ""
% 23.31/3.54  --stdin                                 false
% 23.31/3.54  --stats_out                             all
% 23.31/3.54  
% 23.31/3.54  ------ General Options
% 23.31/3.54  
% 23.31/3.54  --fof                                   false
% 23.31/3.54  --time_out_real                         305.
% 23.31/3.54  --time_out_virtual                      -1.
% 23.31/3.54  --symbol_type_check                     false
% 23.31/3.54  --clausify_out                          false
% 23.31/3.54  --sig_cnt_out                           false
% 23.31/3.54  --trig_cnt_out                          false
% 23.31/3.54  --trig_cnt_out_tolerance                1.
% 23.31/3.54  --trig_cnt_out_sk_spl                   false
% 23.31/3.54  --abstr_cl_out                          false
% 23.31/3.54  
% 23.31/3.54  ------ Global Options
% 23.31/3.54  
% 23.31/3.54  --schedule                              default
% 23.31/3.54  --add_important_lit                     false
% 23.31/3.54  --prop_solver_per_cl                    1000
% 23.31/3.54  --min_unsat_core                        false
% 23.31/3.54  --soft_assumptions                      false
% 23.31/3.54  --soft_lemma_size                       3
% 23.31/3.54  --prop_impl_unit_size                   0
% 23.31/3.54  --prop_impl_unit                        []
% 23.31/3.54  --share_sel_clauses                     true
% 23.31/3.54  --reset_solvers                         false
% 23.31/3.54  --bc_imp_inh                            [conj_cone]
% 23.31/3.54  --conj_cone_tolerance                   3.
% 23.31/3.54  --extra_neg_conj                        none
% 23.31/3.54  --large_theory_mode                     true
% 23.31/3.54  --prolific_symb_bound                   200
% 23.31/3.54  --lt_threshold                          2000
% 23.31/3.54  --clause_weak_htbl                      true
% 23.31/3.54  --gc_record_bc_elim                     false
% 23.31/3.54  
% 23.31/3.54  ------ Preprocessing Options
% 23.31/3.54  
% 23.31/3.54  --preprocessing_flag                    true
% 23.31/3.54  --time_out_prep_mult                    0.1
% 23.31/3.54  --splitting_mode                        input
% 23.31/3.54  --splitting_grd                         true
% 23.31/3.54  --splitting_cvd                         false
% 23.31/3.54  --splitting_cvd_svl                     false
% 23.31/3.54  --splitting_nvd                         32
% 23.31/3.54  --sub_typing                            true
% 23.31/3.54  --prep_gs_sim                           true
% 23.31/3.54  --prep_unflatten                        true
% 23.31/3.54  --prep_res_sim                          true
% 23.31/3.54  --prep_upred                            true
% 23.31/3.54  --prep_sem_filter                       exhaustive
% 23.31/3.54  --prep_sem_filter_out                   false
% 23.31/3.54  --pred_elim                             true
% 23.31/3.54  --res_sim_input                         true
% 23.31/3.54  --eq_ax_congr_red                       true
% 23.31/3.54  --pure_diseq_elim                       true
% 23.31/3.54  --brand_transform                       false
% 23.31/3.54  --non_eq_to_eq                          false
% 23.31/3.54  --prep_def_merge                        true
% 23.31/3.54  --prep_def_merge_prop_impl              false
% 23.31/3.54  --prep_def_merge_mbd                    true
% 23.31/3.54  --prep_def_merge_tr_red                 false
% 23.31/3.54  --prep_def_merge_tr_cl                  false
% 23.31/3.54  --smt_preprocessing                     true
% 23.31/3.54  --smt_ac_axioms                         fast
% 23.31/3.54  --preprocessed_out                      false
% 23.31/3.54  --preprocessed_stats                    false
% 23.31/3.54  
% 23.31/3.54  ------ Abstraction refinement Options
% 23.31/3.54  
% 23.31/3.54  --abstr_ref                             []
% 23.31/3.54  --abstr_ref_prep                        false
% 23.31/3.54  --abstr_ref_until_sat                   false
% 23.31/3.54  --abstr_ref_sig_restrict                funpre
% 23.31/3.54  --abstr_ref_af_restrict_to_split_sk     false
% 23.31/3.54  --abstr_ref_under                       []
% 23.31/3.54  
% 23.31/3.54  ------ SAT Options
% 23.31/3.54  
% 23.31/3.54  --sat_mode                              false
% 23.31/3.54  --sat_fm_restart_options                ""
% 23.31/3.54  --sat_gr_def                            false
% 23.31/3.54  --sat_epr_types                         true
% 23.31/3.54  --sat_non_cyclic_types                  false
% 23.31/3.54  --sat_finite_models                     false
% 23.31/3.54  --sat_fm_lemmas                         false
% 23.31/3.54  --sat_fm_prep                           false
% 23.31/3.54  --sat_fm_uc_incr                        true
% 23.31/3.54  --sat_out_model                         small
% 23.31/3.54  --sat_out_clauses                       false
% 23.31/3.54  
% 23.31/3.54  ------ QBF Options
% 23.31/3.54  
% 23.31/3.54  --qbf_mode                              false
% 23.31/3.54  --qbf_elim_univ                         false
% 23.31/3.54  --qbf_dom_inst                          none
% 23.31/3.54  --qbf_dom_pre_inst                      false
% 23.31/3.54  --qbf_sk_in                             false
% 23.31/3.54  --qbf_pred_elim                         true
% 23.31/3.54  --qbf_split                             512
% 23.31/3.54  
% 23.31/3.54  ------ BMC1 Options
% 23.31/3.54  
% 23.31/3.54  --bmc1_incremental                      false
% 23.31/3.54  --bmc1_axioms                           reachable_all
% 23.31/3.54  --bmc1_min_bound                        0
% 23.31/3.54  --bmc1_max_bound                        -1
% 23.31/3.54  --bmc1_max_bound_default                -1
% 23.31/3.54  --bmc1_symbol_reachability              true
% 23.31/3.54  --bmc1_property_lemmas                  false
% 23.31/3.54  --bmc1_k_induction                      false
% 23.31/3.54  --bmc1_non_equiv_states                 false
% 23.31/3.54  --bmc1_deadlock                         false
% 23.31/3.54  --bmc1_ucm                              false
% 23.31/3.54  --bmc1_add_unsat_core                   none
% 23.31/3.54  --bmc1_unsat_core_children              false
% 23.31/3.54  --bmc1_unsat_core_extrapolate_axioms    false
% 23.31/3.54  --bmc1_out_stat                         full
% 23.31/3.54  --bmc1_ground_init                      false
% 23.31/3.54  --bmc1_pre_inst_next_state              false
% 23.31/3.54  --bmc1_pre_inst_state                   false
% 23.31/3.54  --bmc1_pre_inst_reach_state             false
% 23.31/3.54  --bmc1_out_unsat_core                   false
% 23.31/3.54  --bmc1_aig_witness_out                  false
% 23.31/3.54  --bmc1_verbose                          false
% 23.31/3.54  --bmc1_dump_clauses_tptp                false
% 23.31/3.54  --bmc1_dump_unsat_core_tptp             false
% 23.31/3.54  --bmc1_dump_file                        -
% 23.31/3.54  --bmc1_ucm_expand_uc_limit              128
% 23.31/3.54  --bmc1_ucm_n_expand_iterations          6
% 23.31/3.54  --bmc1_ucm_extend_mode                  1
% 23.31/3.54  --bmc1_ucm_init_mode                    2
% 23.31/3.54  --bmc1_ucm_cone_mode                    none
% 23.31/3.54  --bmc1_ucm_reduced_relation_type        0
% 23.31/3.54  --bmc1_ucm_relax_model                  4
% 23.31/3.54  --bmc1_ucm_full_tr_after_sat            true
% 23.31/3.54  --bmc1_ucm_expand_neg_assumptions       false
% 23.31/3.54  --bmc1_ucm_layered_model                none
% 23.31/3.54  --bmc1_ucm_max_lemma_size               10
% 23.31/3.54  
% 23.31/3.54  ------ AIG Options
% 23.31/3.54  
% 23.31/3.54  --aig_mode                              false
% 23.31/3.54  
% 23.31/3.54  ------ Instantiation Options
% 23.31/3.54  
% 23.31/3.54  --instantiation_flag                    true
% 23.31/3.54  --inst_sos_flag                         true
% 23.31/3.54  --inst_sos_phase                        true
% 23.31/3.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.31/3.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.31/3.54  --inst_lit_sel_side                     num_symb
% 23.31/3.54  --inst_solver_per_active                1400
% 23.31/3.54  --inst_solver_calls_frac                1.
% 23.31/3.54  --inst_passive_queue_type               priority_queues
% 23.31/3.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.31/3.54  --inst_passive_queues_freq              [25;2]
% 23.31/3.54  --inst_dismatching                      true
% 23.31/3.54  --inst_eager_unprocessed_to_passive     true
% 23.31/3.54  --inst_prop_sim_given                   true
% 23.31/3.54  --inst_prop_sim_new                     false
% 23.31/3.54  --inst_subs_new                         false
% 23.31/3.54  --inst_eq_res_simp                      false
% 23.31/3.54  --inst_subs_given                       false
% 23.31/3.54  --inst_orphan_elimination               true
% 23.31/3.54  --inst_learning_loop_flag               true
% 23.31/3.54  --inst_learning_start                   3000
% 23.31/3.54  --inst_learning_factor                  2
% 23.31/3.54  --inst_start_prop_sim_after_learn       3
% 23.31/3.54  --inst_sel_renew                        solver
% 23.31/3.54  --inst_lit_activity_flag                true
% 23.31/3.54  --inst_restr_to_given                   false
% 23.31/3.54  --inst_activity_threshold               500
% 23.31/3.54  --inst_out_proof                        true
% 23.31/3.54  
% 23.31/3.54  ------ Resolution Options
% 23.31/3.54  
% 23.31/3.54  --resolution_flag                       true
% 23.31/3.54  --res_lit_sel                           adaptive
% 23.31/3.54  --res_lit_sel_side                      none
% 23.31/3.54  --res_ordering                          kbo
% 23.31/3.54  --res_to_prop_solver                    active
% 23.31/3.54  --res_prop_simpl_new                    false
% 23.31/3.54  --res_prop_simpl_given                  true
% 23.31/3.54  --res_passive_queue_type                priority_queues
% 23.31/3.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.31/3.54  --res_passive_queues_freq               [15;5]
% 23.31/3.54  --res_forward_subs                      full
% 23.31/3.54  --res_backward_subs                     full
% 23.31/3.54  --res_forward_subs_resolution           true
% 23.31/3.54  --res_backward_subs_resolution          true
% 23.31/3.54  --res_orphan_elimination                true
% 23.31/3.54  --res_time_limit                        2.
% 23.31/3.54  --res_out_proof                         true
% 23.31/3.54  
% 23.31/3.54  ------ Superposition Options
% 23.31/3.54  
% 23.31/3.54  --superposition_flag                    true
% 23.31/3.54  --sup_passive_queue_type                priority_queues
% 23.31/3.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.31/3.54  --sup_passive_queues_freq               [8;1;4]
% 23.31/3.54  --demod_completeness_check              fast
% 23.31/3.54  --demod_use_ground                      true
% 23.31/3.54  --sup_to_prop_solver                    passive
% 23.31/3.54  --sup_prop_simpl_new                    true
% 23.31/3.54  --sup_prop_simpl_given                  true
% 23.31/3.54  --sup_fun_splitting                     true
% 23.31/3.54  --sup_smt_interval                      50000
% 23.31/3.54  
% 23.31/3.54  ------ Superposition Simplification Setup
% 23.31/3.54  
% 23.31/3.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.31/3.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.31/3.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.31/3.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.31/3.54  --sup_full_triv                         [TrivRules;PropSubs]
% 23.31/3.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.31/3.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.31/3.54  --sup_immed_triv                        [TrivRules]
% 23.31/3.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.31/3.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.31/3.54  --sup_immed_bw_main                     []
% 23.31/3.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.31/3.54  --sup_input_triv                        [Unflattening;TrivRules]
% 23.31/3.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.31/3.54  --sup_input_bw                          []
% 23.31/3.54  
% 23.31/3.54  ------ Combination Options
% 23.31/3.54  
% 23.31/3.54  --comb_res_mult                         3
% 23.31/3.54  --comb_sup_mult                         2
% 23.31/3.54  --comb_inst_mult                        10
% 23.31/3.54  
% 23.31/3.54  ------ Debug Options
% 23.31/3.54  
% 23.31/3.54  --dbg_backtrace                         false
% 23.31/3.54  --dbg_dump_prop_clauses                 false
% 23.31/3.54  --dbg_dump_prop_clauses_file            -
% 23.31/3.54  --dbg_out_stat                          false
% 23.31/3.54  ------ Parsing...
% 23.31/3.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.31/3.54  
% 23.31/3.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 23.31/3.54  
% 23.31/3.54  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.31/3.54  
% 23.31/3.54  ------ Preprocessing... sf_s  rm: 13 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.31/3.54  ------ Proving...
% 23.31/3.54  ------ Problem Properties 
% 23.31/3.54  
% 23.31/3.54  
% 23.31/3.54  clauses                                 139
% 23.31/3.54  conjectures                             3
% 23.31/3.54  EPR                                     5
% 23.31/3.54  Horn                                    112
% 23.31/3.54  unary                                   38
% 23.31/3.54  binary                                  29
% 23.31/3.54  lits                                    500
% 23.31/3.54  lits eq                                 172
% 23.31/3.54  fd_pure                                 0
% 23.31/3.54  fd_pseudo                               0
% 23.31/3.54  fd_cond                                 30
% 23.31/3.54  fd_pseudo_cond                          0
% 23.31/3.54  AC symbols                              0
% 23.31/3.54  
% 23.31/3.54  ------ Schedule dynamic 5 is on 
% 23.31/3.54  
% 23.31/3.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.31/3.54  
% 23.31/3.54  
% 23.31/3.54  ------ 
% 23.31/3.54  Current options:
% 23.31/3.54  ------ 
% 23.31/3.54  
% 23.31/3.54  ------ Input Options
% 23.31/3.54  
% 23.31/3.54  --out_options                           all
% 23.31/3.54  --tptp_safe_out                         true
% 23.31/3.54  --problem_path                          ""
% 23.31/3.54  --include_path                          ""
% 23.31/3.54  --clausifier                            res/vclausify_rel
% 23.31/3.54  --clausifier_options                    ""
% 23.31/3.54  --stdin                                 false
% 23.31/3.54  --stats_out                             all
% 23.31/3.54  
% 23.31/3.54  ------ General Options
% 23.31/3.54  
% 23.31/3.54  --fof                                   false
% 23.31/3.54  --time_out_real                         305.
% 23.31/3.54  --time_out_virtual                      -1.
% 23.31/3.54  --symbol_type_check                     false
% 23.31/3.54  --clausify_out                          false
% 23.31/3.54  --sig_cnt_out                           false
% 23.31/3.54  --trig_cnt_out                          false
% 23.31/3.54  --trig_cnt_out_tolerance                1.
% 23.31/3.54  --trig_cnt_out_sk_spl                   false
% 23.31/3.54  --abstr_cl_out                          false
% 23.31/3.54  
% 23.31/3.54  ------ Global Options
% 23.31/3.54  
% 23.31/3.54  --schedule                              default
% 23.31/3.54  --add_important_lit                     false
% 23.31/3.54  --prop_solver_per_cl                    1000
% 23.31/3.54  --min_unsat_core                        false
% 23.31/3.54  --soft_assumptions                      false
% 23.31/3.54  --soft_lemma_size                       3
% 23.31/3.54  --prop_impl_unit_size                   0
% 23.31/3.54  --prop_impl_unit                        []
% 23.31/3.54  --share_sel_clauses                     true
% 23.31/3.54  --reset_solvers                         false
% 23.31/3.54  --bc_imp_inh                            [conj_cone]
% 23.31/3.54  --conj_cone_tolerance                   3.
% 23.31/3.54  --extra_neg_conj                        none
% 23.31/3.54  --large_theory_mode                     true
% 23.31/3.54  --prolific_symb_bound                   200
% 23.31/3.54  --lt_threshold                          2000
% 23.31/3.54  --clause_weak_htbl                      true
% 23.31/3.54  --gc_record_bc_elim                     false
% 23.31/3.54  
% 23.31/3.54  ------ Preprocessing Options
% 23.31/3.54  
% 23.31/3.54  --preprocessing_flag                    true
% 23.31/3.54  --time_out_prep_mult                    0.1
% 23.31/3.54  --splitting_mode                        input
% 23.31/3.54  --splitting_grd                         true
% 23.31/3.54  --splitting_cvd                         false
% 23.31/3.54  --splitting_cvd_svl                     false
% 23.31/3.54  --splitting_nvd                         32
% 23.31/3.54  --sub_typing                            true
% 23.31/3.54  --prep_gs_sim                           true
% 23.31/3.54  --prep_unflatten                        true
% 23.31/3.54  --prep_res_sim                          true
% 23.31/3.54  --prep_upred                            true
% 23.31/3.54  --prep_sem_filter                       exhaustive
% 23.31/3.54  --prep_sem_filter_out                   false
% 23.31/3.54  --pred_elim                             true
% 23.31/3.54  --res_sim_input                         true
% 23.31/3.54  --eq_ax_congr_red                       true
% 23.31/3.54  --pure_diseq_elim                       true
% 23.31/3.54  --brand_transform                       false
% 23.31/3.54  --non_eq_to_eq                          false
% 23.31/3.54  --prep_def_merge                        true
% 23.31/3.54  --prep_def_merge_prop_impl              false
% 23.31/3.54  --prep_def_merge_mbd                    true
% 23.31/3.54  --prep_def_merge_tr_red                 false
% 23.31/3.54  --prep_def_merge_tr_cl                  false
% 23.31/3.54  --smt_preprocessing                     true
% 23.31/3.54  --smt_ac_axioms                         fast
% 23.31/3.54  --preprocessed_out                      false
% 23.31/3.54  --preprocessed_stats                    false
% 23.31/3.54  
% 23.31/3.54  ------ Abstraction refinement Options
% 23.31/3.54  
% 23.31/3.54  --abstr_ref                             []
% 23.31/3.54  --abstr_ref_prep                        false
% 23.31/3.54  --abstr_ref_until_sat                   false
% 23.31/3.54  --abstr_ref_sig_restrict                funpre
% 23.31/3.54  --abstr_ref_af_restrict_to_split_sk     false
% 23.31/3.54  --abstr_ref_under                       []
% 23.31/3.54  
% 23.31/3.54  ------ SAT Options
% 23.31/3.54  
% 23.31/3.54  --sat_mode                              false
% 23.31/3.54  --sat_fm_restart_options                ""
% 23.31/3.54  --sat_gr_def                            false
% 23.31/3.54  --sat_epr_types                         true
% 23.31/3.54  --sat_non_cyclic_types                  false
% 23.31/3.54  --sat_finite_models                     false
% 23.31/3.54  --sat_fm_lemmas                         false
% 23.31/3.54  --sat_fm_prep                           false
% 23.31/3.54  --sat_fm_uc_incr                        true
% 23.31/3.54  --sat_out_model                         small
% 23.31/3.54  --sat_out_clauses                       false
% 23.31/3.54  
% 23.31/3.54  ------ QBF Options
% 23.31/3.54  
% 23.31/3.54  --qbf_mode                              false
% 23.31/3.54  --qbf_elim_univ                         false
% 23.31/3.54  --qbf_dom_inst                          none
% 23.31/3.54  --qbf_dom_pre_inst                      false
% 23.31/3.54  --qbf_sk_in                             false
% 23.31/3.54  --qbf_pred_elim                         true
% 23.31/3.54  --qbf_split                             512
% 23.31/3.54  
% 23.31/3.54  ------ BMC1 Options
% 23.31/3.54  
% 23.31/3.54  --bmc1_incremental                      false
% 23.31/3.54  --bmc1_axioms                           reachable_all
% 23.31/3.54  --bmc1_min_bound                        0
% 23.31/3.54  --bmc1_max_bound                        -1
% 23.31/3.54  --bmc1_max_bound_default                -1
% 23.31/3.54  --bmc1_symbol_reachability              true
% 23.31/3.54  --bmc1_property_lemmas                  false
% 23.31/3.54  --bmc1_k_induction                      false
% 23.31/3.54  --bmc1_non_equiv_states                 false
% 23.31/3.54  --bmc1_deadlock                         false
% 23.31/3.54  --bmc1_ucm                              false
% 23.31/3.54  --bmc1_add_unsat_core                   none
% 23.31/3.54  --bmc1_unsat_core_children              false
% 23.31/3.54  --bmc1_unsat_core_extrapolate_axioms    false
% 23.31/3.54  --bmc1_out_stat                         full
% 23.31/3.54  --bmc1_ground_init                      false
% 23.31/3.54  --bmc1_pre_inst_next_state              false
% 23.31/3.54  --bmc1_pre_inst_state                   false
% 23.31/3.54  --bmc1_pre_inst_reach_state             false
% 23.31/3.54  --bmc1_out_unsat_core                   false
% 23.31/3.54  --bmc1_aig_witness_out                  false
% 23.31/3.54  --bmc1_verbose                          false
% 23.31/3.54  --bmc1_dump_clauses_tptp                false
% 23.31/3.54  --bmc1_dump_unsat_core_tptp             false
% 23.31/3.54  --bmc1_dump_file                        -
% 23.31/3.54  --bmc1_ucm_expand_uc_limit              128
% 23.31/3.54  --bmc1_ucm_n_expand_iterations          6
% 23.31/3.54  --bmc1_ucm_extend_mode                  1
% 23.31/3.54  --bmc1_ucm_init_mode                    2
% 23.31/3.54  --bmc1_ucm_cone_mode                    none
% 23.31/3.54  --bmc1_ucm_reduced_relation_type        0
% 23.31/3.54  --bmc1_ucm_relax_model                  4
% 23.31/3.54  --bmc1_ucm_full_tr_after_sat            true
% 23.31/3.54  --bmc1_ucm_expand_neg_assumptions       false
% 23.31/3.54  --bmc1_ucm_layered_model                none
% 23.31/3.54  --bmc1_ucm_max_lemma_size               10
% 23.31/3.54  
% 23.31/3.54  ------ AIG Options
% 23.31/3.54  
% 23.31/3.54  --aig_mode                              false
% 23.31/3.54  
% 23.31/3.54  ------ Instantiation Options
% 23.31/3.54  
% 23.31/3.54  --instantiation_flag                    true
% 23.31/3.54  --inst_sos_flag                         true
% 23.31/3.54  --inst_sos_phase                        true
% 23.31/3.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.31/3.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.31/3.54  --inst_lit_sel_side                     none
% 23.31/3.54  --inst_solver_per_active                1400
% 23.31/3.54  --inst_solver_calls_frac                1.
% 23.31/3.54  --inst_passive_queue_type               priority_queues
% 23.31/3.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.31/3.54  --inst_passive_queues_freq              [25;2]
% 23.31/3.54  --inst_dismatching                      true
% 23.31/3.54  --inst_eager_unprocessed_to_passive     true
% 23.31/3.54  --inst_prop_sim_given                   true
% 23.31/3.54  --inst_prop_sim_new                     false
% 23.31/3.54  --inst_subs_new                         false
% 23.31/3.54  --inst_eq_res_simp                      false
% 23.31/3.54  --inst_subs_given                       false
% 23.31/3.54  --inst_orphan_elimination               true
% 23.31/3.54  --inst_learning_loop_flag               true
% 23.31/3.54  --inst_learning_start                   3000
% 23.31/3.54  --inst_learning_factor                  2
% 23.31/3.54  --inst_start_prop_sim_after_learn       3
% 23.31/3.54  --inst_sel_renew                        solver
% 23.31/3.54  --inst_lit_activity_flag                true
% 23.31/3.54  --inst_restr_to_given                   false
% 23.31/3.54  --inst_activity_threshold               500
% 23.31/3.54  --inst_out_proof                        true
% 23.31/3.54  
% 23.31/3.54  ------ Resolution Options
% 23.31/3.54  
% 23.31/3.54  --resolution_flag                       false
% 23.31/3.54  --res_lit_sel                           adaptive
% 23.31/3.54  --res_lit_sel_side                      none
% 23.31/3.54  --res_ordering                          kbo
% 23.31/3.54  --res_to_prop_solver                    active
% 23.31/3.54  --res_prop_simpl_new                    false
% 23.31/3.54  --res_prop_simpl_given                  true
% 23.31/3.54  --res_passive_queue_type                priority_queues
% 23.31/3.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.31/3.54  --res_passive_queues_freq               [15;5]
% 23.31/3.54  --res_forward_subs                      full
% 23.31/3.54  --res_backward_subs                     full
% 23.31/3.54  --res_forward_subs_resolution           true
% 23.31/3.54  --res_backward_subs_resolution          true
% 23.31/3.54  --res_orphan_elimination                true
% 23.31/3.54  --res_time_limit                        2.
% 23.31/3.54  --res_out_proof                         true
% 23.31/3.54  
% 23.31/3.54  ------ Superposition Options
% 23.31/3.54  
% 23.31/3.54  --superposition_flag                    true
% 23.31/3.54  --sup_passive_queue_type                priority_queues
% 23.31/3.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.31/3.54  --sup_passive_queues_freq               [8;1;4]
% 23.31/3.54  --demod_completeness_check              fast
% 23.31/3.54  --demod_use_ground                      true
% 23.31/3.54  --sup_to_prop_solver                    passive
% 23.31/3.54  --sup_prop_simpl_new                    true
% 23.31/3.54  --sup_prop_simpl_given                  true
% 23.31/3.54  --sup_fun_splitting                     true
% 23.31/3.54  --sup_smt_interval                      50000
% 23.31/3.54  
% 23.31/3.54  ------ Superposition Simplification Setup
% 23.31/3.54  
% 23.31/3.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.31/3.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.31/3.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.31/3.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.31/3.54  --sup_full_triv                         [TrivRules;PropSubs]
% 23.31/3.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.31/3.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.31/3.54  --sup_immed_triv                        [TrivRules]
% 23.31/3.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.31/3.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.31/3.54  --sup_immed_bw_main                     []
% 23.31/3.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.31/3.54  --sup_input_triv                        [Unflattening;TrivRules]
% 23.31/3.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.31/3.54  --sup_input_bw                          []
% 23.31/3.54  
% 23.31/3.54  ------ Combination Options
% 23.31/3.54  
% 23.31/3.54  --comb_res_mult                         3
% 23.31/3.54  --comb_sup_mult                         2
% 23.31/3.54  --comb_inst_mult                        10
% 23.31/3.54  
% 23.31/3.54  ------ Debug Options
% 23.31/3.54  
% 23.31/3.54  --dbg_backtrace                         false
% 23.31/3.54  --dbg_dump_prop_clauses                 false
% 23.31/3.54  --dbg_dump_prop_clauses_file            -
% 23.31/3.54  --dbg_out_stat                          false
% 23.31/3.54  
% 23.31/3.54  
% 23.31/3.54  
% 23.31/3.54  
% 23.31/3.54  ------ Proving...
% 23.31/3.54  
% 23.31/3.54  
% 23.31/3.54  % SZS status Theorem for theBenchmark.p
% 23.31/3.54  
% 23.31/3.54  % SZS output start CNFRefutation for theBenchmark.p
% 23.31/3.54  
% 23.31/3.54  fof(f17,axiom,(
% 23.31/3.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f49,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.31/3.54    inference(ennf_transformation,[],[f17])).
% 23.31/3.54  
% 23.31/3.54  fof(f100,plain,(
% 23.31/3.54    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f49])).
% 23.31/3.54  
% 23.31/3.54  fof(f19,conjecture,(
% 23.31/3.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f20,negated_conjecture,(
% 23.31/3.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 23.31/3.54    inference(negated_conjecture,[],[f19])).
% 23.31/3.54  
% 23.31/3.54  fof(f51,plain,(
% 23.31/3.54    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 23.31/3.54    inference(ennf_transformation,[],[f20])).
% 23.31/3.54  
% 23.31/3.54  fof(f52,plain,(
% 23.31/3.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.31/3.54    inference(flattening,[],[f51])).
% 23.31/3.54  
% 23.31/3.54  fof(f65,plain,(
% 23.31/3.54    ( ! [X2,X0,X1] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) => (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),sK5) & m1_subset_1(sK5,u1_struct_0(X2)))) )),
% 23.31/3.54    introduced(choice_axiom,[])).
% 23.31/3.54  
% 23.31/3.54  fof(f64,plain,(
% 23.31/3.54    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK4,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK4),X3) & m1_subset_1(X3,u1_struct_0(sK4))) & r1_tsep_1(X1,sK4) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 23.31/3.54    introduced(choice_axiom,[])).
% 23.31/3.54  
% 23.31/3.54  fof(f63,plain,(
% 23.31/3.54    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(sK3,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 23.31/3.54    introduced(choice_axiom,[])).
% 23.31/3.54  
% 23.31/3.54  fof(f62,plain,(
% 23.31/3.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 23.31/3.54    introduced(choice_axiom,[])).
% 23.31/3.54  
% 23.31/3.54  fof(f66,plain,(
% 23.31/3.54    (((~r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) & m1_subset_1(sK5,u1_struct_0(sK4))) & r1_tsep_1(sK3,sK4) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 23.31/3.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f52,f65,f64,f63,f62])).
% 23.31/3.54  
% 23.31/3.54  fof(f106,plain,(
% 23.31/3.54    m1_pre_topc(sK3,sK2)),
% 23.31/3.54    inference(cnf_transformation,[],[f66])).
% 23.31/3.54  
% 23.31/3.54  fof(f104,plain,(
% 23.31/3.54    l1_pre_topc(sK2)),
% 23.31/3.54    inference(cnf_transformation,[],[f66])).
% 23.31/3.54  
% 23.31/3.54  fof(f6,axiom,(
% 23.31/3.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f28,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.31/3.54    inference(ennf_transformation,[],[f6])).
% 23.31/3.54  
% 23.31/3.54  fof(f29,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(flattening,[],[f28])).
% 23.31/3.54  
% 23.31/3.54  fof(f72,plain,(
% 23.31/3.54    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f29])).
% 23.31/3.54  
% 23.31/3.54  fof(f102,plain,(
% 23.31/3.54    ~v2_struct_0(sK2)),
% 23.31/3.54    inference(cnf_transformation,[],[f66])).
% 23.31/3.54  
% 23.31/3.54  fof(f103,plain,(
% 23.31/3.54    v2_pre_topc(sK2)),
% 23.31/3.54    inference(cnf_transformation,[],[f66])).
% 23.31/3.54  
% 23.31/3.54  fof(f7,axiom,(
% 23.31/3.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f30,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.31/3.54    inference(ennf_transformation,[],[f7])).
% 23.31/3.54  
% 23.31/3.54  fof(f31,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(flattening,[],[f30])).
% 23.31/3.54  
% 23.31/3.54  fof(f53,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(nnf_transformation,[],[f31])).
% 23.31/3.54  
% 23.31/3.54  fof(f54,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(rectify,[],[f53])).
% 23.31/3.54  
% 23.31/3.54  fof(f55,plain,(
% 23.31/3.54    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.31/3.54    introduced(choice_axiom,[])).
% 23.31/3.54  
% 23.31/3.54  fof(f56,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).
% 23.31/3.54  
% 23.31/3.54  fof(f73,plain,(
% 23.31/3.54    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f56])).
% 23.31/3.54  
% 23.31/3.54  fof(f112,plain,(
% 23.31/3.54    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(equality_resolution,[],[f73])).
% 23.31/3.54  
% 23.31/3.54  fof(f113,plain,(
% 23.31/3.54    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(equality_resolution,[],[f112])).
% 23.31/3.54  
% 23.31/3.54  fof(f12,axiom,(
% 23.31/3.54    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f39,plain,(
% 23.31/3.54    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.31/3.54    inference(ennf_transformation,[],[f12])).
% 23.31/3.54  
% 23.31/3.54  fof(f40,plain,(
% 23.31/3.54    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(flattening,[],[f39])).
% 23.31/3.54  
% 23.31/3.54  fof(f89,plain,(
% 23.31/3.54    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f40])).
% 23.31/3.54  
% 23.31/3.54  fof(f90,plain,(
% 23.31/3.54    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f40])).
% 23.31/3.54  
% 23.31/3.54  fof(f91,plain,(
% 23.31/3.54    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f40])).
% 23.31/3.54  
% 23.31/3.54  fof(f11,axiom,(
% 23.31/3.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f37,plain,(
% 23.31/3.54    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.31/3.54    inference(ennf_transformation,[],[f11])).
% 23.31/3.54  
% 23.31/3.54  fof(f38,plain,(
% 23.31/3.54    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(flattening,[],[f37])).
% 23.31/3.54  
% 23.31/3.54  fof(f88,plain,(
% 23.31/3.54    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f38])).
% 23.31/3.54  
% 23.31/3.54  fof(f16,axiom,(
% 23.31/3.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f47,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.31/3.54    inference(ennf_transformation,[],[f16])).
% 23.31/3.54  
% 23.31/3.54  fof(f48,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(flattening,[],[f47])).
% 23.31/3.54  
% 23.31/3.54  fof(f98,plain,(
% 23.31/3.54    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f48])).
% 23.31/3.54  
% 23.31/3.54  fof(f105,plain,(
% 23.31/3.54    ~v2_struct_0(sK3)),
% 23.31/3.54    inference(cnf_transformation,[],[f66])).
% 23.31/3.54  
% 23.31/3.54  fof(f8,axiom,(
% 23.31/3.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f32,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.31/3.54    inference(ennf_transformation,[],[f8])).
% 23.31/3.54  
% 23.31/3.54  fof(f33,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(flattening,[],[f32])).
% 23.31/3.54  
% 23.31/3.54  fof(f57,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(nnf_transformation,[],[f33])).
% 23.31/3.54  
% 23.31/3.54  fof(f58,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(rectify,[],[f57])).
% 23.31/3.54  
% 23.31/3.54  fof(f59,plain,(
% 23.31/3.54    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.31/3.54    introduced(choice_axiom,[])).
% 23.31/3.54  
% 23.31/3.54  fof(f60,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).
% 23.31/3.54  
% 23.31/3.54  fof(f79,plain,(
% 23.31/3.54    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f60])).
% 23.31/3.54  
% 23.31/3.54  fof(f108,plain,(
% 23.31/3.54    m1_pre_topc(sK4,sK2)),
% 23.31/3.54    inference(cnf_transformation,[],[f66])).
% 23.31/3.54  
% 23.31/3.54  fof(f107,plain,(
% 23.31/3.54    ~v2_struct_0(sK4)),
% 23.31/3.54    inference(cnf_transformation,[],[f66])).
% 23.31/3.54  
% 23.31/3.54  fof(f87,plain,(
% 23.31/3.54    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f38])).
% 23.31/3.54  
% 23.31/3.54  fof(f86,plain,(
% 23.31/3.54    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f38])).
% 23.31/3.54  
% 23.31/3.54  fof(f5,axiom,(
% 23.31/3.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f26,plain,(
% 23.31/3.54    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 23.31/3.54    inference(ennf_transformation,[],[f5])).
% 23.31/3.54  
% 23.31/3.54  fof(f27,plain,(
% 23.31/3.54    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 23.31/3.54    inference(flattening,[],[f26])).
% 23.31/3.54  
% 23.31/3.54  fof(f71,plain,(
% 23.31/3.54    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f27])).
% 23.31/3.54  
% 23.31/3.54  fof(f80,plain,(
% 23.31/3.54    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f60])).
% 23.31/3.54  
% 23.31/3.54  fof(f4,axiom,(
% 23.31/3.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f24,plain,(
% 23.31/3.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 23.31/3.54    inference(ennf_transformation,[],[f4])).
% 23.31/3.54  
% 23.31/3.54  fof(f25,plain,(
% 23.31/3.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(flattening,[],[f24])).
% 23.31/3.54  
% 23.31/3.54  fof(f70,plain,(
% 23.31/3.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f25])).
% 23.31/3.54  
% 23.31/3.54  fof(f2,axiom,(
% 23.31/3.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f22,plain,(
% 23.31/3.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 23.31/3.54    inference(ennf_transformation,[],[f2])).
% 23.31/3.54  
% 23.31/3.54  fof(f68,plain,(
% 23.31/3.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f22])).
% 23.31/3.54  
% 23.31/3.54  fof(f78,plain,(
% 23.31/3.54    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f60])).
% 23.31/3.54  
% 23.31/3.54  fof(f13,axiom,(
% 23.31/3.54    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f41,plain,(
% 23.31/3.54    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.31/3.54    inference(ennf_transformation,[],[f13])).
% 23.31/3.54  
% 23.31/3.54  fof(f42,plain,(
% 23.31/3.54    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(flattening,[],[f41])).
% 23.31/3.54  
% 23.31/3.54  fof(f94,plain,(
% 23.31/3.54    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f42])).
% 23.31/3.54  
% 23.31/3.54  fof(f92,plain,(
% 23.31/3.54    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f42])).
% 23.31/3.54  
% 23.31/3.54  fof(f93,plain,(
% 23.31/3.54    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f42])).
% 23.31/3.54  
% 23.31/3.54  fof(f77,plain,(
% 23.31/3.54    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f60])).
% 23.31/3.54  
% 23.31/3.54  fof(f114,plain,(
% 23.31/3.54    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(equality_resolution,[],[f77])).
% 23.31/3.54  
% 23.31/3.54  fof(f115,plain,(
% 23.31/3.54    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(equality_resolution,[],[f114])).
% 23.31/3.54  
% 23.31/3.54  fof(f15,axiom,(
% 23.31/3.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f45,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.31/3.54    inference(ennf_transformation,[],[f15])).
% 23.31/3.54  
% 23.31/3.54  fof(f46,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.31/3.54    inference(flattening,[],[f45])).
% 23.31/3.54  
% 23.31/3.54  fof(f97,plain,(
% 23.31/3.54    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f46])).
% 23.31/3.54  
% 23.31/3.54  fof(f111,plain,(
% 23.31/3.54    ~r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5)),
% 23.31/3.54    inference(cnf_transformation,[],[f66])).
% 23.31/3.54  
% 23.31/3.54  fof(f110,plain,(
% 23.31/3.54    m1_subset_1(sK5,u1_struct_0(sK4))),
% 23.31/3.54    inference(cnf_transformation,[],[f66])).
% 23.31/3.54  
% 23.31/3.54  fof(f3,axiom,(
% 23.31/3.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f23,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.31/3.54    inference(ennf_transformation,[],[f3])).
% 23.31/3.54  
% 23.31/3.54  fof(f69,plain,(
% 23.31/3.54    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f23])).
% 23.31/3.54  
% 23.31/3.54  fof(f9,axiom,(
% 23.31/3.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f34,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 23.31/3.54    inference(ennf_transformation,[],[f9])).
% 23.31/3.54  
% 23.31/3.54  fof(f61,plain,(
% 23.31/3.54    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 23.31/3.54    inference(nnf_transformation,[],[f34])).
% 23.31/3.54  
% 23.31/3.54  fof(f81,plain,(
% 23.31/3.54    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f61])).
% 23.31/3.54  
% 23.31/3.54  fof(f109,plain,(
% 23.31/3.54    r1_tsep_1(sK3,sK4)),
% 23.31/3.54    inference(cnf_transformation,[],[f66])).
% 23.31/3.54  
% 23.31/3.54  fof(f1,axiom,(
% 23.31/3.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 23.31/3.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.31/3.54  
% 23.31/3.54  fof(f21,plain,(
% 23.31/3.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 23.31/3.54    inference(ennf_transformation,[],[f1])).
% 23.31/3.54  
% 23.31/3.54  fof(f67,plain,(
% 23.31/3.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 23.31/3.54    inference(cnf_transformation,[],[f21])).
% 23.31/3.54  
% 23.31/3.54  cnf(c_33,plain,
% 23.31/3.54      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.54      | ~ m1_pre_topc(X0,X1)
% 23.31/3.54      | ~ l1_pre_topc(X1) ),
% 23.31/3.54      inference(cnf_transformation,[],[f100]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_40,negated_conjecture,
% 23.31/3.54      ( m1_pre_topc(sK3,sK2) ),
% 23.31/3.54      inference(cnf_transformation,[],[f106]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1363,plain,
% 23.31/3.54      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.54      | ~ l1_pre_topc(X1)
% 23.31/3.54      | sK3 != X0
% 23.31/3.54      | sK2 != X1 ),
% 23.31/3.54      inference(resolution_lifted,[status(thm)],[c_33,c_40]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1364,plain,
% 23.31/3.54      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.54      | ~ l1_pre_topc(sK2) ),
% 23.31/3.54      inference(unflattening,[status(thm)],[c_1363]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_42,negated_conjecture,
% 23.31/3.54      ( l1_pre_topc(sK2) ),
% 23.31/3.54      inference(cnf_transformation,[],[f104]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1366,plain,
% 23.31/3.54      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 23.31/3.54      inference(global_propositional_subsumption,
% 23.31/3.54                [status(thm)],
% 23.31/3.54                [c_1364,c_42]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_15753,plain,
% 23.31/3.54      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 23.31/3.54      inference(subtyping,[status(esa)],[c_1366]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_17892,plain,
% 23.31/3.54      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 23.31/3.54      inference(predicate_to_equality,[status(thm)],[c_15753]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_5,plain,
% 23.31/3.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ l1_pre_topc(X1)
% 23.31/3.54      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 23.31/3.54      inference(cnf_transformation,[],[f72]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_44,negated_conjecture,
% 23.31/3.54      ( ~ v2_struct_0(sK2) ),
% 23.31/3.54      inference(cnf_transformation,[],[f102]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_4486,plain,
% 23.31/3.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | ~ l1_pre_topc(X1)
% 23.31/3.54      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 23.31/3.54      | sK2 != X1 ),
% 23.31/3.54      inference(resolution_lifted,[status(thm)],[c_5,c_44]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_4487,plain,
% 23.31/3.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.54      | ~ v2_pre_topc(sK2)
% 23.31/3.54      | ~ l1_pre_topc(sK2)
% 23.31/3.54      | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.54      inference(unflattening,[status(thm)],[c_4486]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_43,negated_conjecture,
% 23.31/3.54      ( v2_pre_topc(sK2) ),
% 23.31/3.54      inference(cnf_transformation,[],[f103]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_4491,plain,
% 23.31/3.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.54      | k7_tmap_1(sK2,X0) = k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.54      inference(global_propositional_subsumption,
% 23.31/3.54                [status(thm)],
% 23.31/3.54                [c_4487,c_43,c_42]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_15693,plain,
% 23.31/3.54      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.54      | k7_tmap_1(sK2,X0_59) = k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.54      inference(subtyping,[status(esa)],[c_4491]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_17951,plain,
% 23.31/3.54      ( k7_tmap_1(sK2,X0_59) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.54      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 23.31/3.54      inference(predicate_to_equality,[status(thm)],[c_15693]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_19906,plain,
% 23.31/3.54      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.54      inference(superposition,[status(thm)],[c_17892,c_17951]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_9,plain,
% 23.31/3.54      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.54      | ~ m1_pre_topc(X0,X1)
% 23.31/3.54      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ l1_pre_topc(X1)
% 23.31/3.54      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 23.31/3.54      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 23.31/3.54      inference(cnf_transformation,[],[f113]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_24,plain,
% 23.31/3.54      ( ~ m1_pre_topc(X0,X1)
% 23.31/3.54      | v1_pre_topc(k8_tmap_1(X1,X0))
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ l1_pre_topc(X1) ),
% 23.31/3.54      inference(cnf_transformation,[],[f89]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_23,plain,
% 23.31/3.54      ( ~ m1_pre_topc(X0,X1)
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | v2_pre_topc(k8_tmap_1(X1,X0))
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ l1_pre_topc(X1) ),
% 23.31/3.54      inference(cnf_transformation,[],[f90]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_22,plain,
% 23.31/3.54      ( ~ m1_pre_topc(X0,X1)
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ l1_pre_topc(X1)
% 23.31/3.54      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 23.31/3.54      inference(cnf_transformation,[],[f91]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_294,plain,
% 23.31/3.54      ( ~ l1_pre_topc(X1)
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ m1_pre_topc(X0,X1)
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 23.31/3.54      inference(global_propositional_subsumption,
% 23.31/3.54                [status(thm)],
% 23.31/3.54                [c_9,c_33,c_24,c_23,c_22]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_295,plain,
% 23.31/3.54      ( ~ m1_pre_topc(X0,X1)
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ l1_pre_topc(X1)
% 23.31/3.54      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 23.31/3.54      inference(renaming,[status(thm)],[c_294]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1347,plain,
% 23.31/3.54      ( ~ v2_pre_topc(X0)
% 23.31/3.54      | v2_struct_0(X0)
% 23.31/3.54      | ~ l1_pre_topc(X0)
% 23.31/3.54      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 23.31/3.54      | sK3 != X1
% 23.31/3.54      | sK2 != X0 ),
% 23.31/3.54      inference(resolution_lifted,[status(thm)],[c_295,c_40]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1348,plain,
% 23.31/3.54      ( ~ v2_pre_topc(sK2)
% 23.31/3.54      | v2_struct_0(sK2)
% 23.31/3.54      | ~ l1_pre_topc(sK2)
% 23.31/3.54      | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 23.31/3.54      inference(unflattening,[status(thm)],[c_1347]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1350,plain,
% 23.31/3.54      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 23.31/3.54      inference(global_propositional_subsumption,
% 23.31/3.54                [status(thm)],
% 23.31/3.54                [c_1348,c_44,c_43,c_42]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_15755,plain,
% 23.31/3.54      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 23.31/3.54      inference(subtyping,[status(esa)],[c_1350]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_19,plain,
% 23.31/3.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.54      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ l1_pre_topc(X1) ),
% 23.31/3.54      inference(cnf_transformation,[],[f88]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_4414,plain,
% 23.31/3.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.54      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | ~ l1_pre_topc(X1)
% 23.31/3.54      | sK2 != X1 ),
% 23.31/3.54      inference(resolution_lifted,[status(thm)],[c_19,c_44]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_4415,plain,
% 23.31/3.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.54      | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))))
% 23.31/3.54      | ~ v2_pre_topc(sK2)
% 23.31/3.54      | ~ l1_pre_topc(sK2) ),
% 23.31/3.54      inference(unflattening,[status(thm)],[c_4414]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_4419,plain,
% 23.31/3.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.54      | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0))))) ),
% 23.31/3.54      inference(global_propositional_subsumption,
% 23.31/3.54                [status(thm)],
% 23.31/3.54                [c_4415,c_43,c_42]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_15697,plain,
% 23.31/3.54      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.54      | m1_subset_1(k7_tmap_1(sK2,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_59))))) ),
% 23.31/3.54      inference(subtyping,[status(esa)],[c_4419]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_17947,plain,
% 23.31/3.54      ( m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.54      | m1_subset_1(k7_tmap_1(sK2,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_59))))) = iProver_top ),
% 23.31/3.54      inference(predicate_to_equality,[status(thm)],[c_15697]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_20607,plain,
% 23.31/3.54      ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
% 23.31/3.54      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 23.31/3.54      inference(superposition,[status(thm)],[c_15755,c_17947]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_32,plain,
% 23.31/3.54      ( ~ m1_pre_topc(X0,X1)
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | v2_struct_0(X0)
% 23.31/3.54      | ~ l1_pre_topc(X1)
% 23.31/3.54      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 23.31/3.54      inference(cnf_transformation,[],[f98]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1374,plain,
% 23.31/3.54      ( ~ v2_pre_topc(X0)
% 23.31/3.54      | v2_struct_0(X0)
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ l1_pre_topc(X0)
% 23.31/3.54      | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
% 23.31/3.54      | sK3 != X1
% 23.31/3.54      | sK2 != X0 ),
% 23.31/3.54      inference(resolution_lifted,[status(thm)],[c_32,c_40]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1375,plain,
% 23.31/3.54      ( ~ v2_pre_topc(sK2)
% 23.31/3.54      | v2_struct_0(sK3)
% 23.31/3.54      | v2_struct_0(sK2)
% 23.31/3.54      | ~ l1_pre_topc(sK2)
% 23.31/3.54      | u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 23.31/3.54      inference(unflattening,[status(thm)],[c_1374]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_41,negated_conjecture,
% 23.31/3.54      ( ~ v2_struct_0(sK3) ),
% 23.31/3.54      inference(cnf_transformation,[],[f105]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1377,plain,
% 23.31/3.54      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 23.31/3.54      inference(global_propositional_subsumption,
% 23.31/3.54                [status(thm)],
% 23.31/3.54                [c_1375,c_44,c_43,c_42,c_41]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_15752,plain,
% 23.31/3.54      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 23.31/3.54      inference(subtyping,[status(esa)],[c_1377]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_20608,plain,
% 23.31/3.54      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
% 23.31/3.54      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 23.31/3.54      inference(light_normalisation,
% 23.31/3.54                [status(thm)],
% 23.31/3.54                [c_20607,c_15752,c_19906]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_47,plain,
% 23.31/3.54      ( l1_pre_topc(sK2) = iProver_top ),
% 23.31/3.54      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1365,plain,
% 23.31/3.54      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 23.31/3.54      | l1_pre_topc(sK2) != iProver_top ),
% 23.31/3.54      inference(predicate_to_equality,[status(thm)],[c_1364]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_20615,plain,
% 23.31/3.54      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 23.31/3.54      inference(global_propositional_subsumption,
% 23.31/3.54                [status(thm)],
% 23.31/3.54                [c_20608,c_47,c_1365]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_11,plain,
% 23.31/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 23.31/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 23.31/3.54      | ~ m1_pre_topc(X2,X1)
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | ~ v1_funct_1(X0)
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ l1_pre_topc(X1)
% 23.31/3.54      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 23.31/3.54      | k9_tmap_1(X1,X2) = X0 ),
% 23.31/3.54      inference(cnf_transformation,[],[f79]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_38,negated_conjecture,
% 23.31/3.54      ( m1_pre_topc(sK4,sK2) ),
% 23.31/3.54      inference(cnf_transformation,[],[f108]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1872,plain,
% 23.31/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 23.31/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 23.31/3.54      | ~ v2_pre_topc(X1)
% 23.31/3.54      | ~ v1_funct_1(X0)
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ l1_pre_topc(X1)
% 23.31/3.54      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 23.31/3.54      | k9_tmap_1(X1,X2) = X0
% 23.31/3.54      | sK2 != X1
% 23.31/3.54      | sK4 != X2 ),
% 23.31/3.54      inference(resolution_lifted,[status(thm)],[c_11,c_38]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1873,plain,
% 23.31/3.54      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.54      | ~ v2_pre_topc(sK2)
% 23.31/3.54      | ~ v1_funct_1(X0)
% 23.31/3.54      | v2_struct_0(sK2)
% 23.31/3.54      | ~ l1_pre_topc(sK2)
% 23.31/3.54      | sK1(sK2,sK4,X0) = u1_struct_0(sK4)
% 23.31/3.54      | k9_tmap_1(sK2,sK4) = X0 ),
% 23.31/3.54      inference(unflattening,[status(thm)],[c_1872]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1877,plain,
% 23.31/3.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.54      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.54      | ~ v1_funct_1(X0)
% 23.31/3.54      | sK1(sK2,sK4,X0) = u1_struct_0(sK4)
% 23.31/3.54      | k9_tmap_1(sK2,sK4) = X0 ),
% 23.31/3.54      inference(global_propositional_subsumption,
% 23.31/3.54                [status(thm)],
% 23.31/3.54                [c_1873,c_44,c_43,c_42]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1878,plain,
% 23.31/3.54      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.54      | ~ v1_funct_1(X0)
% 23.31/3.54      | sK1(sK2,sK4,X0) = u1_struct_0(sK4)
% 23.31/3.54      | k9_tmap_1(sK2,sK4) = X0 ),
% 23.31/3.54      inference(renaming,[status(thm)],[c_1877]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_15737,plain,
% 23.31/3.54      ( ~ v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.54      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.54      | ~ v1_funct_1(X0_59)
% 23.31/3.54      | sK1(sK2,sK4,X0_59) = u1_struct_0(sK4)
% 23.31/3.54      | k9_tmap_1(sK2,sK4) = X0_59 ),
% 23.31/3.54      inference(subtyping,[status(esa)],[c_1878]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_17907,plain,
% 23.31/3.54      ( sK1(sK2,sK4,X0_59) = u1_struct_0(sK4)
% 23.31/3.54      | k9_tmap_1(sK2,sK4) = X0_59
% 23.31/3.54      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))) != iProver_top
% 23.31/3.54      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))))) != iProver_top
% 23.31/3.54      | v1_funct_1(X0_59) != iProver_top ),
% 23.31/3.54      inference(predicate_to_equality,[status(thm)],[c_15737]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1230,plain,
% 23.31/3.54      ( ~ v2_pre_topc(X0)
% 23.31/3.54      | v2_struct_0(X0)
% 23.31/3.54      | v2_struct_0(X1)
% 23.31/3.54      | ~ l1_pre_topc(X0)
% 23.31/3.54      | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
% 23.31/3.54      | sK2 != X0
% 23.31/3.54      | sK4 != X1 ),
% 23.31/3.54      inference(resolution_lifted,[status(thm)],[c_32,c_38]) ).
% 23.31/3.54  
% 23.31/3.54  cnf(c_1231,plain,
% 23.31/3.54      ( ~ v2_pre_topc(sK2)
% 23.31/3.54      | v2_struct_0(sK2)
% 23.31/3.54      | v2_struct_0(sK4)
% 23.31/3.54      | ~ l1_pre_topc(sK2)
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK4)) = u1_struct_0(sK2) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1230]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_39,negated_conjecture,
% 23.31/3.55      ( ~ v2_struct_0(sK4) ),
% 23.31/3.55      inference(cnf_transformation,[],[f107]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1233,plain,
% 23.31/3.55      ( u1_struct_0(k8_tmap_1(sK2,sK4)) = u1_struct_0(sK2) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_1231,c_44,c_43,c_42,c_39]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15763,plain,
% 23.31/3.55      ( u1_struct_0(k8_tmap_1(sK2,sK4)) = u1_struct_0(sK2) ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_1233]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_18015,plain,
% 23.31/3.55      ( sK1(sK2,sK4,X0_59) = u1_struct_0(sK4)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X0_59
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_17907,c_15763]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_21552,plain,
% 23.31/3.55      ( sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK4)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_20615,c_18015]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_20,plain,
% 23.31/3.55      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 23.31/3.55      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 23.31/3.55      | ~ v2_pre_topc(X0)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f87]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5119,plain,
% 23.31/3.55      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 23.31/3.55      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 23.31/3.55      | ~ v2_pre_topc(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0)
% 23.31/3.55      | sK2 != X0 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_20,c_44]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5120,plain,
% 23.31/3.55      ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | ~ v2_pre_topc(sK2)
% 23.31/3.55      | ~ l1_pre_topc(sK2) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_5119]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5124,plain,
% 23.31/3.55      ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_5120,c_43,c_42]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15660,plain,
% 23.31/3.55      ( v1_funct_2(k7_tmap_1(sK2,X0_59),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_59)))
% 23.31/3.55      | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_5124]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17981,plain,
% 23.31/3.55      ( v1_funct_2(k7_tmap_1(sK2,X0_59),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_59))) = iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15660]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_20066,plain,
% 23.31/3.55      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
% 23.31/3.55      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_15755,c_17981]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_20067,plain,
% 23.31/3.55      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
% 23.31/3.55      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 23.31/3.55      inference(light_normalisation,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_20066,c_15752,c_19906]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1219,plain,
% 23.31/3.55      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | sK2 != X1
% 23.31/3.55      | sK4 != X0 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_33,c_38]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1220,plain,
% 23.31/3.55      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | ~ l1_pre_topc(sK2) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1219]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1222,plain,
% 23.31/3.55      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_1220,c_42]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15764,plain,
% 23.31/3.55      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_1222]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17884,plain,
% 23.31/3.55      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15764]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_21,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | v1_funct_1(k7_tmap_1(X1,X0))
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_pre_topc(X1) ),
% 23.31/3.55      inference(cnf_transformation,[],[f86]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_4396,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | v1_funct_1(k7_tmap_1(X1,X0))
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | sK2 != X1 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_21,c_44]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_4397,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | ~ v2_pre_topc(sK2)
% 23.31/3.55      | v1_funct_1(k7_tmap_1(sK2,X0))
% 23.31/3.55      | ~ l1_pre_topc(sK2) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_4396]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_4401,plain,
% 23.31/3.55      ( v1_funct_1(k7_tmap_1(sK2,X0))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_4397,c_43,c_42]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_4402,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | v1_funct_1(k7_tmap_1(sK2,X0)) ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_4401]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15698,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | v1_funct_1(k7_tmap_1(sK2,X0_59)) ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_4402]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17946,plain,
% 23.31/3.55      ( m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | v1_funct_1(k7_tmap_1(sK2,X0_59)) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15698]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_19498,plain,
% 23.31/3.55      ( v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK4))) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_17884,c_17946]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_19905,plain,
% 23.31/3.55      ( k7_tmap_1(sK2,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_17884,c_17951]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_22870,plain,
% 23.31/3.55      ( v1_funct_1(k6_partfun1(u1_struct_0(sK2))) = iProver_top ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_19498,c_19905]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25756,plain,
% 23.31/3.55      ( sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))) = u1_struct_0(sK4)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_21552,c_47,c_1365,c_20067,c_22870]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_4,plain,
% 23.31/3.55      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 23.31/3.55      | ~ v1_funct_2(X5,X2,X3)
% 23.31/3.55      | ~ v1_funct_2(X4,X0,X1)
% 23.31/3.55      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 23.31/3.55      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.31/3.55      | ~ v1_funct_1(X5)
% 23.31/3.55      | ~ v1_funct_1(X4)
% 23.31/3.55      | v1_xboole_0(X1)
% 23.31/3.55      | v1_xboole_0(X3) ),
% 23.31/3.55      inference(cnf_transformation,[],[f71]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_10,plain,
% 23.31/3.55      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 23.31/3.55      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 23.31/3.55      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 23.31/3.55      | ~ m1_pre_topc(X1,X0)
% 23.31/3.55      | ~ v2_pre_topc(X0)
% 23.31/3.55      | ~ v1_funct_1(X2)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0)
% 23.31/3.55      | k9_tmap_1(X0,X1) = X2 ),
% 23.31/3.55      inference(cnf_transformation,[],[f80]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1644,plain,
% 23.31/3.55      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 23.31/3.55      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 23.31/3.55      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 23.31/3.55      | ~ v2_pre_topc(X0)
% 23.31/3.55      | ~ v1_funct_1(X2)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0)
% 23.31/3.55      | k9_tmap_1(X0,X1) = X2
% 23.31/3.55      | sK2 != X0
% 23.31/3.55      | sK4 != X1 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_10,c_38]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1645,plain,
% 23.31/3.55      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK4,X0)))
% 23.31/3.55      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v2_pre_topc(sK2)
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | v2_struct_0(sK2)
% 23.31/3.55      | ~ l1_pre_topc(sK2)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X0 ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1644]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1649,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK4,X0)))
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X0 ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_1645,c_44,c_43,c_42]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1650,plain,
% 23.31/3.55      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK4,X0)))
% 23.31/3.55      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X0 ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_1649]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5452,plain,
% 23.31/3.55      ( ~ v1_funct_2(X0,X1,X2)
% 23.31/3.55      | ~ v1_funct_2(X3,X4,X5)
% 23.31/3.55      | ~ v1_funct_2(X6,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.31/3.55      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 23.31/3.55      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | ~ v1_funct_1(X3)
% 23.31/3.55      | ~ v1_funct_1(X6)
% 23.31/3.55      | v1_xboole_0(X2)
% 23.31/3.55      | v1_xboole_0(X5)
% 23.31/3.55      | X6 != X3
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X6
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,X6)) != X3
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X6))) != X2
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK4)) != X5
% 23.31/3.55      | u1_struct_0(sK2) != X1
% 23.31/3.55      | u1_struct_0(sK2) != X4 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_4,c_1650]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5453,plain,
% 23.31/3.55      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1))))
% 23.31/3.55      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1))))))
% 23.31/3.55      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | ~ v1_funct_1(X1)
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1))))
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X1
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,X1)) != X1 ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_5452]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15732,plain,
% 23.31/3.55      ( ~ v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1_59))))
% 23.31/3.55      | ~ v1_funct_2(X1_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1_59))))))
% 23.31/3.55      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_1(X0_59)
% 23.31/3.55      | ~ v1_funct_1(X1_59)
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X1_59))))
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X1_59
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,X1_59)) != X1_59 ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_5453]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17912,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = X0_59
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,X0_59)) != X0_59
% 23.31/3.55      | v1_funct_2(X1_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) != iProver_top
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))) != iProver_top
% 23.31/3.55      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))))) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))))) != iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top
% 23.31/3.55      | v1_funct_1(X1_59) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) = iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK4))) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15732]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_18045,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = X0_59
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,X0_59)) != X0_59
% 23.31/3.55      | v1_funct_2(X1_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) != iProver_top
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))))) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 23.31/3.55      | v1_funct_1(X1_59) != iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) = iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_17912,c_15763]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_45,plain,
% 23.31/3.55      ( v2_struct_0(sK2) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_3,plain,
% 23.31/3.55      ( v2_struct_0(X0)
% 23.31/3.55      | ~ v1_xboole_0(u1_struct_0(X0))
% 23.31/3.55      | ~ l1_struct_0(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f70]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_148,plain,
% 23.31/3.55      ( v2_struct_0(X0) = iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 23.31/3.55      | l1_struct_0(X0) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_150,plain,
% 23.31/3.55      ( v2_struct_0(sK2) = iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | l1_struct_0(sK2) != iProver_top ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_148]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1,plain,
% 23.31/3.55      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f68]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_152,plain,
% 23.31/3.55      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_154,plain,
% 23.31/3.55      ( l1_pre_topc(sK2) != iProver_top
% 23.31/3.55      | l1_struct_0(sK2) = iProver_top ),
% 23.31/3.55      inference(instantiation,[status(thm)],[c_152]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_22572,plain,
% 23.31/3.55      ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) = iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top
% 23.31/3.55      | v1_funct_1(X1_59) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 23.31/3.55      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))))) != iProver_top
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | v1_funct_2(X1_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) != iProver_top
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,X0_59)) != X0_59
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X0_59 ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_18045,c_45,c_47,c_150,c_154]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_22573,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = X0_59
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,X0_59)) != X0_59
% 23.31/3.55      | v1_funct_2(X1_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) != iProver_top
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))))) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 23.31/3.55      | v1_funct_1(X1_59) != iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0_59)))) = iProver_top ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_22572]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25758,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | k7_tmap_1(sK2,u1_struct_0(sK4)) != k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 23.31/3.55      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 23.31/3.55      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top
% 23.31/3.55      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_25756,c_22573]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25759,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | k6_partfun1(u1_struct_0(sK2)) != k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 23.31/3.55      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 23.31/3.55      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top
% 23.31/3.55      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_25758,c_19905]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25760,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 23.31/3.55      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 23.31/3.55      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top
% 23.31/3.55      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 23.31/3.55      inference(equality_resolution_simp,[status(thm)],[c_25759]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_87378,plain,
% 23.31/3.55      ( v1_funct_1(X0_59) != iProver_top
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_25760,c_47,c_1365,c_20067,c_20608,c_22870]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_87379,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) != iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_87378]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_87394,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK4)))))) != iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_25756,c_87379]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1203,plain,
% 23.31/3.55      ( ~ v2_pre_topc(X0)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0)
% 23.31/3.55      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 23.31/3.55      | sK2 != X0
% 23.31/3.55      | sK4 != X1 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_295,c_38]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1204,plain,
% 23.31/3.55      ( ~ v2_pre_topc(sK2)
% 23.31/3.55      | v2_struct_0(sK2)
% 23.31/3.55      | ~ l1_pre_topc(sK2)
% 23.31/3.55      | k6_tmap_1(sK2,u1_struct_0(sK4)) = k8_tmap_1(sK2,sK4) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1203]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1206,plain,
% 23.31/3.55      ( k6_tmap_1(sK2,u1_struct_0(sK4)) = k8_tmap_1(sK2,sK4) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_1204,c_44,c_43,c_42]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15766,plain,
% 23.31/3.55      ( k6_tmap_1(sK2,u1_struct_0(sK4)) = k8_tmap_1(sK2,sK4) ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_1206]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_87395,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 23.31/3.55      inference(light_normalisation,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_87394,c_15763,c_15766]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_12,plain,
% 23.31/3.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 23.31/3.55      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ m1_pre_topc(X2,X1)
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | k9_tmap_1(X1,X2) = X0 ),
% 23.31/3.55      inference(cnf_transformation,[],[f78]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1845,plain,
% 23.31/3.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 23.31/3.55      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | k9_tmap_1(X1,X2) = X0
% 23.31/3.55      | sK2 != X1
% 23.31/3.55      | sK4 != X2 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_12,c_38]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1846,plain,
% 23.31/3.55      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | m1_subset_1(sK1(sK2,sK4,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | ~ v2_pre_topc(sK2)
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | v2_struct_0(sK2)
% 23.31/3.55      | ~ l1_pre_topc(sK2)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X0 ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1845]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1850,plain,
% 23.31/3.55      ( m1_subset_1(sK1(sK2,sK4,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X0 ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_1846,c_44,c_43,c_42]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1851,plain,
% 23.31/3.55      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | m1_subset_1(sK1(sK2,sK4,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X0 ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_1850]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15738,plain,
% 23.31/3.55      ( ~ v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | m1_subset_1(sK1(sK2,sK4,X0_59),k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | ~ v1_funct_1(X0_59)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X0_59 ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_1851]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17906,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = X0_59
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))))) != iProver_top
% 23.31/3.55      | m1_subset_1(sK1(sK2,sK4,X0_59),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15738]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_18018,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = X0_59
% 23.31/3.55      | v1_funct_2(X0_59,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 23.31/3.55      | m1_subset_1(sK1(sK2,sK4,X0_59),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 23.31/3.55      | v1_funct_1(X0_59) != iProver_top ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_17906,c_15763]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_22006,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | m1_subset_1(sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 23.31/3.55      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_20615,c_18018]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_28805,plain,
% 23.31/3.55      ( m1_subset_1(sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_22006,c_47,c_1365,c_20067,c_22870]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_28806,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | m1_subset_1(sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_28805]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_28811,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))) = k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_28806,c_17951]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_29126,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top
% 23.31/3.55      | m1_subset_1(sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_28811,c_17981]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_29580,plain,
% 23.31/3.55      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_29126,c_47,c_1365,c_20067,c_22006,c_22870]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_29581,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_29580]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_29125,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | m1_subset_1(sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_28811,c_17947]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_31443,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))))) = iProver_top ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_29125,c_47,c_1365,c_20067,c_22006,c_22870]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_87385,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) != iProver_top
% 23.31/3.55      | v1_funct_1(k6_partfun1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_31443,c_87379]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_87409,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k6_partfun1(u1_struct_0(sK2)))))) = iProver_top ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_87395,c_22870,c_29581,c_87385]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_87421,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK4)))) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_25756,c_87409]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_87422,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 23.31/3.55      inference(light_normalisation,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_87421,c_15763,c_15766]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_87513,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_87422,c_45,c_47,c_150,c_154]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25,plain,
% 23.31/3.55      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 23.31/3.55      | ~ m1_pre_topc(X1,X0)
% 23.31/3.55      | ~ v2_pre_topc(X0)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f94]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1720,plain,
% 23.31/3.55      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 23.31/3.55      | ~ v2_pre_topc(X0)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0)
% 23.31/3.55      | sK3 != X1
% 23.31/3.55      | sK2 != X0 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_25,c_40]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1721,plain,
% 23.31/3.55      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 23.31/3.55      | ~ v2_pre_topc(sK2)
% 23.31/3.55      | v2_struct_0(sK2)
% 23.31/3.55      | ~ l1_pre_topc(sK2) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1720]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1723,plain,
% 23.31/3.55      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_1721,c_44,c_43,c_42]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15740,plain,
% 23.31/3.55      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_1723]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17904,plain,
% 23.31/3.55      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15740]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_18013,plain,
% 23.31/3.55      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_17904,c_15752]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_21550,plain,
% 23.31/3.55      ( sK1(sK2,sK4,k9_tmap_1(sK2,sK3)) = u1_struct_0(sK4)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_18013,c_18015]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_46,plain,
% 23.31/3.55      ( v2_pre_topc(sK2) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_27,plain,
% 23.31/3.55      ( ~ m1_pre_topc(X0,X1)
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | v1_funct_1(k9_tmap_1(X1,X0))
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_pre_topc(X1) ),
% 23.31/3.55      inference(cnf_transformation,[],[f92]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1382,plain,
% 23.31/3.55      ( ~ v2_pre_topc(X0)
% 23.31/3.55      | v1_funct_1(k9_tmap_1(X0,X1))
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0)
% 23.31/3.55      | sK3 != X1
% 23.31/3.55      | sK2 != X0 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_27,c_40]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1383,plain,
% 23.31/3.55      ( ~ v2_pre_topc(sK2)
% 23.31/3.55      | v1_funct_1(k9_tmap_1(sK2,sK3))
% 23.31/3.55      | v2_struct_0(sK2)
% 23.31/3.55      | ~ l1_pre_topc(sK2) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1382]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1384,plain,
% 23.31/3.55      ( v2_pre_topc(sK2) != iProver_top
% 23.31/3.55      | v1_funct_1(k9_tmap_1(sK2,sK3)) = iProver_top
% 23.31/3.55      | v2_struct_0(sK2) = iProver_top
% 23.31/3.55      | l1_pre_topc(sK2) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_1383]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_26,plain,
% 23.31/3.55      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 23.31/3.55      | ~ m1_pre_topc(X1,X0)
% 23.31/3.55      | ~ v2_pre_topc(X0)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f93]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1709,plain,
% 23.31/3.55      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 23.31/3.55      | ~ v2_pre_topc(X0)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0)
% 23.31/3.55      | sK3 != X1
% 23.31/3.55      | sK2 != X0 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_26,c_40]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1710,plain,
% 23.31/3.55      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 23.31/3.55      | ~ v2_pre_topc(sK2)
% 23.31/3.55      | v2_struct_0(sK2)
% 23.31/3.55      | ~ l1_pre_topc(sK2) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1709]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1712,plain,
% 23.31/3.55      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_1710,c_44,c_43,c_42]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15741,plain,
% 23.31/3.55      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_1712]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17903,plain,
% 23.31/3.55      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15741]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_18010,plain,
% 23.31/3.55      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_17903,c_15752]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25512,plain,
% 23.31/3.55      ( sK1(sK2,sK4,k9_tmap_1(sK2,sK3)) = u1_struct_0(sK4)
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_21550,c_45,c_46,c_47,c_1384,c_18010]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_13,plain,
% 23.31/3.55      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 23.31/3.55      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 23.31/3.55      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 23.31/3.55      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 23.31/3.55      | ~ m1_pre_topc(X1,X0)
% 23.31/3.55      | ~ v2_pre_topc(X0)
% 23.31/3.55      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f115]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_284,plain,
% 23.31/3.55      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 23.31/3.55      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 23.31/3.55      | ~ m1_pre_topc(X1,X0)
% 23.31/3.55      | ~ v2_pre_topc(X0)
% 23.31/3.55      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_13,c_26,c_25]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1698,plain,
% 23.31/3.55      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 23.31/3.55      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 23.31/3.55      | ~ v2_pre_topc(X0)
% 23.31/3.55      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X0)
% 23.31/3.55      | sK3 != X1
% 23.31/3.55      | sK2 != X0 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_284,c_40]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1699,plain,
% 23.31/3.55      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 23.31/3.55      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | ~ v2_pre_topc(sK2)
% 23.31/3.55      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 23.31/3.55      | v2_struct_0(sK2)
% 23.31/3.55      | ~ l1_pre_topc(sK2) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1698]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1701,plain,
% 23.31/3.55      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3))) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_1699,c_44,c_43,c_42,c_1364,c_1383]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5870,plain,
% 23.31/3.55      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | k9_tmap_1(sK2,sK3) != X0
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X0
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,X0)) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4))
% 23.31/3.55      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_1650,c_1701]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5871,plain,
% 23.31/3.55      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_5870]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2607,plain,
% 23.31/3.55      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_1(X0)
% 23.31/3.55      | k9_tmap_1(sK2,sK3) != X0
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = X0
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,X0)) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,X0))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4))
% 23.31/3.55      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_1650,c_1701]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2608,plain,
% 23.31/3.55      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_2607]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2610,plain,
% 23.31/3.55      ( ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_2608,c_44,c_43,c_42,c_1383]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2611,plain,
% 23.31/3.55      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_2610]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5873,plain,
% 23.31/3.55      ( ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_5871,c_44,c_43,c_42,c_1383,c_2608]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_5874,plain,
% 23.31/3.55      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_5873]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15729,plain,
% 23.31/3.55      ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))
% 23.31/3.55      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4)))))
% 23.31/3.55      | k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4)) ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_5874]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17915,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))
% 23.31/3.55      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(k8_tmap_1(sK2,sK4))
% 23.31/3.55      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))) != iProver_top
% 23.31/3.55      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK4))))) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15729]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_18023,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
% 23.31/3.55      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 23.31/3.55      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 23.31/3.55      inference(light_normalisation,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_17915,c_15752,c_15755,c_15763]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_18024,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2)
% 23.31/3.55      | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 23.31/3.55      | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 23.31/3.55      inference(equality_resolution_simp,[status(thm)],[c_18023]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_23556,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k7_tmap_1(sK2,u1_struct_0(sK3))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_18024,c_18010,c_18013]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_23558,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3)))) != u1_struct_0(sK2) ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_23556,c_19906]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25514,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK4))) != u1_struct_0(sK2) ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_25512,c_23558]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25517,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2))
% 23.31/3.55      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 23.31/3.55      inference(light_normalisation,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_25514,c_15763,c_15766]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25518,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,sK1(sK2,sK4,k9_tmap_1(sK2,sK3))) != k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.55      inference(equality_resolution_simp,[status(thm)],[c_25517]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25522,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k7_tmap_1(sK2,u1_struct_0(sK4)) != k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_25512,c_25518]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25523,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3)
% 23.31/3.55      | k6_partfun1(u1_struct_0(sK2)) != k6_partfun1(u1_struct_0(sK2)) ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_25522,c_19905]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_25524,plain,
% 23.31/3.55      ( k9_tmap_1(sK2,sK4) = k9_tmap_1(sK2,sK3) ),
% 23.31/3.55      inference(equality_resolution_simp,[status(thm)],[c_25523]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_30,plain,
% 23.31/3.55      ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
% 23.31/3.55      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 23.31/3.55      | ~ m1_pre_topc(X0,X1)
% 23.31/3.55      | ~ r1_xboole_0(u1_struct_0(X0),X2)
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | v2_struct_0(X0)
% 23.31/3.55      | ~ l1_pre_topc(X1) ),
% 23.31/3.55      inference(cnf_transformation,[],[f97]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_35,negated_conjecture,
% 23.31/3.55      ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
% 23.31/3.55      inference(cnf_transformation,[],[f111]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_519,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 23.31/3.55      | ~ m1_pre_topc(X3,X1)
% 23.31/3.55      | ~ r1_xboole_0(u1_struct_0(X3),X0)
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | v2_struct_0(X3)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),X3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 23.31/3.55      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
% 23.31/3.55      | sK5 != X2
% 23.31/3.55      | sK4 != X3 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_30,c_35]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_520,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 23.31/3.55      | ~ m1_pre_topc(sK4,X1)
% 23.31/3.55      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | v2_struct_0(sK4)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 23.31/3.55      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_519]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_36,negated_conjecture,
% 23.31/3.55      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 23.31/3.55      inference(cnf_transformation,[],[f110]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_524,plain,
% 23.31/3.55      ( v2_struct_0(X1)
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 23.31/3.55      | ~ m1_pre_topc(sK4,X1)
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 23.31/3.55      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_520,c_39,c_36]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_525,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ m1_pre_topc(sK4,X1)
% 23.31/3.55      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 23.31/3.55      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_524]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1980,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.31/3.55      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 23.31/3.55      | ~ v2_pre_topc(X1)
% 23.31/3.55      | v2_struct_0(X1)
% 23.31/3.55      | ~ l1_pre_topc(X1)
% 23.31/3.55      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 23.31/3.55      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
% 23.31/3.55      | sK2 != X1
% 23.31/3.55      | sK4 != sK4 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_38,c_525]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1981,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 23.31/3.55      | ~ v2_pre_topc(sK2)
% 23.31/3.55      | v2_struct_0(sK2)
% 23.31/3.55      | ~ l1_pre_topc(sK2)
% 23.31/3.55      | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 23.31/3.55      | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1980]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1985,plain,
% 23.31/3.55      ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 23.31/3.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 23.31/3.55      | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_1981,c_44,c_43,c_42]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1986,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 23.31/3.55      | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 23.31/3.55      | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
% 23.31/3.55      inference(renaming,[status(thm)],[c_1985]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15733,plain,
% 23.31/3.55      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2)))
% 23.31/3.55      | ~ r1_xboole_0(u1_struct_0(sK4),X0_59)
% 23.31/3.55      | k2_tmap_1(sK2,k6_tmap_1(sK2,X0_59),k7_tmap_1(sK2,X0_59),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 23.31/3.55      | k6_tmap_1(sK2,X0_59) != k8_tmap_1(sK2,sK3) ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_1986]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17911,plain,
% 23.31/3.55      ( k2_tmap_1(sK2,k6_tmap_1(sK2,X0_59),k7_tmap_1(sK2,X0_59),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 23.31/3.55      | k6_tmap_1(sK2,X0_59) != k8_tmap_1(sK2,sK3)
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | r1_xboole_0(u1_struct_0(sK4),X0_59) != iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15733]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_83964,plain,
% 23.31/3.55      ( k2_tmap_1(sK2,k6_tmap_1(sK2,X0_59),k7_tmap_1(sK2,X0_59),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK4),sK4)
% 23.31/3.55      | k6_tmap_1(sK2,X0_59) != k8_tmap_1(sK2,sK3)
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | r1_xboole_0(u1_struct_0(sK4),X0_59) != iProver_top ),
% 23.31/3.55      inference(demodulation,[status(thm)],[c_25524,c_17911]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_87525,plain,
% 23.31/3.55      ( k2_tmap_1(sK2,k6_tmap_1(sK2,X0_59),k7_tmap_1(sK2,X0_59),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK4)
% 23.31/3.55      | k6_tmap_1(sK2,X0_59) != k8_tmap_1(sK2,sK3)
% 23.31/3.55      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | r1_xboole_0(u1_struct_0(sK4),X0_59) != iProver_top ),
% 23.31/3.55      inference(demodulation,[status(thm)],[c_87513,c_83964]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_88347,plain,
% 23.31/3.55      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k6_partfun1(u1_struct_0(sK2)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK4)
% 23.31/3.55      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 23.31/3.55      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_19906,c_87525]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_88396,plain,
% 23.31/3.55      ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK4)
% 23.31/3.55      | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
% 23.31/3.55      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 23.31/3.55      inference(light_normalisation,[status(thm)],[c_88347,c_15755]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_88397,plain,
% 23.31/3.55      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 23.31/3.55      | r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 23.31/3.55      inference(equality_resolution_simp,[status(thm)],[c_88396]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_2,plain,
% 23.31/3.55      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f69]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1480,plain,
% 23.31/3.55      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X1 | sK2 != X0 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_2,c_40]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1481,plain,
% 23.31/3.55      ( l1_pre_topc(sK3) | ~ l1_pre_topc(sK2) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1480]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1483,plain,
% 23.31/3.55      ( l1_pre_topc(sK3) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_1481,c_42]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_10241,plain,
% 23.31/3.55      ( l1_struct_0(X0) | sK3 != X0 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_1,c_1483]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_10242,plain,
% 23.31/3.55      ( l1_struct_0(sK3) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_10241]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1336,plain,
% 23.31/3.55      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK4 != X1 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_2,c_38]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1337,plain,
% 23.31/3.55      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_1336]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_1339,plain,
% 23.31/3.55      ( l1_pre_topc(sK4) ),
% 23.31/3.55      inference(global_propositional_subsumption,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_1337,c_42]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_9784,plain,
% 23.31/3.55      ( l1_struct_0(X0) | sK4 != X0 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_1,c_1339]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_9785,plain,
% 23.31/3.55      ( l1_struct_0(sK4) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_9784]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15,plain,
% 23.31/3.55      ( ~ r1_tsep_1(X0,X1)
% 23.31/3.55      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 23.31/3.55      | ~ l1_struct_0(X0)
% 23.31/3.55      | ~ l1_struct_0(X1) ),
% 23.31/3.55      inference(cnf_transformation,[],[f81]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_37,negated_conjecture,
% 23.31/3.55      ( r1_tsep_1(sK3,sK4) ),
% 23.31/3.55      inference(cnf_transformation,[],[f109]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_565,plain,
% 23.31/3.55      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 23.31/3.55      | ~ l1_struct_0(X1)
% 23.31/3.55      | ~ l1_struct_0(X0)
% 23.31/3.55      | sK3 != X0
% 23.31/3.55      | sK4 != X1 ),
% 23.31/3.55      inference(resolution_lifted,[status(thm)],[c_15,c_37]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_566,plain,
% 23.31/3.55      ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
% 23.31/3.55      | ~ l1_struct_0(sK3)
% 23.31/3.55      | ~ l1_struct_0(sK4) ),
% 23.31/3.55      inference(unflattening,[status(thm)],[c_565]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_12258,plain,
% 23.31/3.55      ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
% 23.31/3.55      | ~ l1_struct_0(sK3) ),
% 23.31/3.55      inference(backward_subsumption_resolution,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_9785,c_566]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_12329,plain,
% 23.31/3.55      ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 23.31/3.55      inference(backward_subsumption_resolution,
% 23.31/3.55                [status(thm)],
% 23.31/3.55                [c_10242,c_12258]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15636,plain,
% 23.31/3.55      ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_12329]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_18007,plain,
% 23.31/3.55      ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15636]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_0,plain,
% 23.31/3.55      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 23.31/3.55      inference(cnf_transformation,[],[f67]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_15771,plain,
% 23.31/3.55      ( ~ r1_xboole_0(X0_59,X1_59) | r1_xboole_0(X1_59,X0_59) ),
% 23.31/3.55      inference(subtyping,[status(esa)],[c_0]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_17879,plain,
% 23.31/3.55      ( r1_xboole_0(X0_59,X1_59) != iProver_top
% 23.31/3.55      | r1_xboole_0(X1_59,X0_59) = iProver_top ),
% 23.31/3.55      inference(predicate_to_equality,[status(thm)],[c_15771]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(c_19056,plain,
% 23.31/3.55      ( r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 23.31/3.55      inference(superposition,[status(thm)],[c_18007,c_17879]) ).
% 23.31/3.55  
% 23.31/3.55  cnf(contradiction,plain,
% 23.31/3.55      ( $false ),
% 23.31/3.55      inference(minisat,[status(thm)],[c_88397,c_19056,c_1365,c_47]) ).
% 23.31/3.55  
% 23.31/3.55  
% 23.31/3.55  % SZS output end CNFRefutation for theBenchmark.p
% 23.31/3.55  
% 23.31/3.55  ------                               Statistics
% 23.31/3.55  
% 23.31/3.55  ------ General
% 23.31/3.55  
% 23.31/3.55  abstr_ref_over_cycles:                  0
% 23.31/3.55  abstr_ref_under_cycles:                 0
% 23.31/3.55  gc_basic_clause_elim:                   0
% 23.31/3.55  forced_gc_time:                         0
% 23.31/3.55  parsing_time:                           0.014
% 23.31/3.55  unif_index_cands_time:                  0.
% 23.31/3.55  unif_index_add_time:                    0.
% 23.31/3.55  orderings_time:                         0.
% 23.31/3.55  out_proof_time:                         0.028
% 23.31/3.55  total_time:                             2.571
% 23.31/3.55  num_of_symbols:                         71
% 23.31/3.55  num_of_terms:                           30607
% 23.31/3.55  
% 23.31/3.55  ------ Preprocessing
% 23.31/3.55  
% 23.31/3.55  num_of_splits:                          2
% 23.31/3.55  num_of_split_atoms:                     2
% 23.31/3.55  num_of_reused_defs:                     0
% 23.31/3.55  num_eq_ax_congr_red:                    11
% 23.31/3.55  num_of_sem_filtered_clauses:            13
% 23.31/3.55  num_of_subtypes:                        4
% 23.31/3.55  monotx_restored_types:                  0
% 23.31/3.55  sat_num_of_epr_types:                   0
% 23.31/3.55  sat_num_of_non_cyclic_types:            0
% 23.31/3.55  sat_guarded_non_collapsed_types:        2
% 23.31/3.55  num_pure_diseq_elim:                    0
% 23.31/3.55  simp_replaced_by:                       0
% 23.31/3.55  res_preprocessed:                       370
% 23.31/3.55  prep_upred:                             0
% 23.31/3.55  prep_unflattend:                        799
% 23.31/3.55  smt_new_axioms:                         0
% 23.31/3.55  pred_elim_cands:                        14
% 23.31/3.55  pred_elim:                              6
% 23.31/3.55  pred_elim_cl:                           -92
% 23.31/3.55  pred_elim_cycles:                       13
% 23.31/3.55  merged_defs:                            0
% 23.31/3.55  merged_defs_ncl:                        0
% 23.31/3.55  bin_hyper_res:                          0
% 23.31/3.55  prep_cycles:                            3
% 23.31/3.55  pred_elim_time:                         0.335
% 23.31/3.55  splitting_time:                         0.
% 23.31/3.55  sem_filter_time:                        0.
% 23.31/3.55  monotx_time:                            0.
% 23.31/3.55  subtype_inf_time:                       0.002
% 23.31/3.55  
% 23.31/3.55  ------ Problem properties
% 23.31/3.55  
% 23.31/3.55  clauses:                                139
% 23.31/3.55  conjectures:                            3
% 23.31/3.55  epr:                                    5
% 23.31/3.55  horn:                                   112
% 23.31/3.55  ground:                                 78
% 23.31/3.55  unary:                                  38
% 23.31/3.55  binary:                                 29
% 23.31/3.55  lits:                                   500
% 23.31/3.55  lits_eq:                                172
% 23.31/3.55  fd_pure:                                0
% 23.31/3.55  fd_pseudo:                              0
% 23.31/3.55  fd_cond:                                30
% 23.31/3.55  fd_pseudo_cond:                         0
% 23.31/3.55  ac_symbols:                             0
% 23.31/3.55  
% 23.31/3.55  ------ Propositional Solver
% 23.31/3.55  
% 23.31/3.55  prop_solver_calls:                      34
% 23.31/3.55  prop_fast_solver_calls:                 14271
% 23.31/3.55  smt_solver_calls:                       0
% 23.31/3.55  smt_fast_solver_calls:                  0
% 23.31/3.55  prop_num_of_clauses:                    19495
% 23.31/3.55  prop_preprocess_simplified:             46114
% 23.31/3.55  prop_fo_subsumed:                       2031
% 23.31/3.55  prop_solver_time:                       0.
% 23.31/3.55  smt_solver_time:                        0.
% 23.31/3.55  smt_fast_solver_time:                   0.
% 23.31/3.55  prop_fast_solver_time:                  0.
% 23.31/3.55  prop_unsat_core_time:                   0.002
% 23.31/3.55  
% 23.31/3.55  ------ QBF
% 23.31/3.55  
% 23.31/3.55  qbf_q_res:                              0
% 23.31/3.55  qbf_num_tautologies:                    0
% 23.31/3.55  qbf_prep_cycles:                        0
% 23.31/3.55  
% 23.31/3.55  ------ BMC1
% 23.31/3.55  
% 23.31/3.55  bmc1_current_bound:                     -1
% 23.31/3.55  bmc1_last_solved_bound:                 -1
% 23.31/3.55  bmc1_unsat_core_size:                   -1
% 23.31/3.55  bmc1_unsat_core_parents_size:           -1
% 23.31/3.55  bmc1_merge_next_fun:                    0
% 23.31/3.55  bmc1_unsat_core_clauses_time:           0.
% 23.31/3.55  
% 23.31/3.55  ------ Instantiation
% 23.31/3.55  
% 23.31/3.55  inst_num_of_clauses:                    2998
% 23.31/3.55  inst_num_in_passive:                    525
% 23.31/3.55  inst_num_in_active:                     3906
% 23.31/3.55  inst_num_in_unprocessed:                881
% 23.31/3.55  inst_num_of_loops:                      4619
% 23.31/3.55  inst_num_of_learning_restarts:          1
% 23.31/3.55  inst_num_moves_active_passive:          704
% 23.31/3.55  inst_lit_activity:                      0
% 23.31/3.55  inst_lit_activity_moves:                1
% 23.31/3.55  inst_num_tautologies:                   0
% 23.31/3.55  inst_num_prop_implied:                  0
% 23.31/3.55  inst_num_existing_simplified:           0
% 23.31/3.55  inst_num_eq_res_simplified:             0
% 23.31/3.55  inst_num_child_elim:                    0
% 23.31/3.55  inst_num_of_dismatching_blockings:      9866
% 23.31/3.55  inst_num_of_non_proper_insts:           11119
% 23.31/3.55  inst_num_of_duplicates:                 0
% 23.31/3.55  inst_inst_num_from_inst_to_res:         0
% 23.31/3.55  inst_dismatching_checking_time:         0.
% 23.31/3.55  
% 23.31/3.55  ------ Resolution
% 23.31/3.55  
% 23.31/3.55  res_num_of_clauses:                     156
% 23.31/3.55  res_num_in_passive:                     156
% 23.31/3.55  res_num_in_active:                      0
% 23.31/3.55  res_num_of_loops:                       373
% 23.31/3.55  res_forward_subset_subsumed:            2075
% 23.31/3.55  res_backward_subset_subsumed:           4
% 23.31/3.55  res_forward_subsumed:                   1
% 23.31/3.55  res_backward_subsumed:                  0
% 23.31/3.55  res_forward_subsumption_resolution:     10
% 23.31/3.55  res_backward_subsumption_resolution:    4
% 23.31/3.55  res_clause_to_clause_subsumption:       15434
% 23.31/3.55  res_orphan_elimination:                 0
% 23.31/3.55  res_tautology_del:                      1913
% 23.31/3.55  res_num_eq_res_simplified:              0
% 23.31/3.55  res_num_sel_changes:                    0
% 23.31/3.55  res_moves_from_active_to_pass:          0
% 23.31/3.55  
% 23.31/3.55  ------ Superposition
% 23.31/3.55  
% 23.31/3.55  sup_time_total:                         0.
% 23.31/3.55  sup_time_generating:                    0.
% 23.31/3.55  sup_time_sim_full:                      0.
% 23.31/3.55  sup_time_sim_immed:                     0.
% 23.31/3.55  
% 23.31/3.55  sup_num_of_clauses:                     1872
% 23.31/3.55  sup_num_in_active:                      704
% 23.31/3.55  sup_num_in_passive:                     1168
% 23.31/3.55  sup_num_of_loops:                       923
% 23.31/3.55  sup_fw_superposition:                   4363
% 23.31/3.55  sup_bw_superposition:                   3155
% 23.31/3.55  sup_immediate_simplified:               4731
% 23.31/3.55  sup_given_eliminated:                   0
% 23.31/3.55  comparisons_done:                       0
% 23.31/3.55  comparisons_avoided:                    1833
% 23.31/3.55  
% 23.31/3.55  ------ Simplifications
% 23.31/3.55  
% 23.31/3.55  
% 23.31/3.55  sim_fw_subset_subsumed:                 1809
% 23.31/3.55  sim_bw_subset_subsumed:                 115
% 23.31/3.55  sim_fw_subsumed:                        1700
% 23.31/3.55  sim_bw_subsumed:                        69
% 23.31/3.55  sim_fw_subsumption_res:                 0
% 23.31/3.55  sim_bw_subsumption_res:                 0
% 23.31/3.55  sim_tautology_del:                      95
% 23.31/3.55  sim_eq_tautology_del:                   248
% 23.31/3.55  sim_eq_res_simp:                        18
% 23.31/3.55  sim_fw_demodulated:                     120
% 23.31/3.55  sim_bw_demodulated:                     99
% 23.31/3.55  sim_light_normalised:                   2503
% 23.31/3.55  sim_joinable_taut:                      0
% 23.31/3.55  sim_joinable_simp:                      0
% 23.31/3.55  sim_ac_normalised:                      0
% 23.31/3.55  sim_smt_subsumption:                    0
% 23.31/3.55  
%------------------------------------------------------------------------------
