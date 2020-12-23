%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1800+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  180 (4232 expanded)
%              Number of clauses        :  129 (1035 expanded)
%              Number of leaves         :   16 ( 980 expanded)
%              Depth                    :   22
%              Number of atoms          :  810 (34034 expanded)
%              Number of equality atoms :  288 (6628 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k8_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k8_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k8_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( k8_tmap_1(X0,sK3) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
          | ~ m1_pre_topc(sK3,X0)
          | ~ v1_tsep_1(sK3,X0) )
        & ( k8_tmap_1(X0,sK3) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
          | ( m1_pre_topc(sK3,X0)
            & v1_tsep_1(sK3,X0) ) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k8_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k8_tmap_1(sK2,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
            | ~ m1_pre_topc(X1,sK2)
            | ~ v1_tsep_1(X1,sK2) )
          & ( k8_tmap_1(sK2,X1) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
            | ( m1_pre_topc(X1,sK2)
              & v1_tsep_1(X1,sK2) ) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | ~ m1_pre_topc(sK3,sK2)
      | ~ v1_tsep_1(sK3,sK2) )
    & ( k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | ( m1_pre_topc(sK3,sK2)
        & v1_tsep_1(sK3,sK2) ) )
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f31,f30])).

fof(f53,plain,
    ( k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK0(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0,X1),X0)
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK1(X0,X1),X0)
                & u1_struct_0(X1) = sK1(X0,X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f52,plain,
    ( k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
            & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK1(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_13,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK2)
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_123,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_17])).

cnf(c_634,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_123])).

cnf(c_635,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_637,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_635,c_19])).

cnf(c_1364,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_637])).

cnf(c_2012,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1364])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0,X2) = u1_struct_0(X0)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_645,plain,
    ( v2_struct_0(X0)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK0(X0,X2,X1) = u1_struct_0(X2)
    | k8_tmap_1(X0,X2) = X1
    | sK3 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_123])).

cnf(c_646,plain,
    ( v2_struct_0(sK2)
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_650,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_21,c_20,c_19])).

cnf(c_651,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_650])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1016,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_1017,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_pre_topc(k6_tmap_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1016])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_pre_topc(k6_tmap_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1017,c_20,c_19])).

cnf(c_1216,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(sK2,sK3,X1) = u1_struct_0(sK3)
    | k6_tmap_1(sK2,X0) != X1
    | k8_tmap_1(sK2,sK3) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_651,c_1021])).

cnf(c_1217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(k6_tmap_1(sK2,X0))
    | ~ l1_pre_topc(k6_tmap_1(sK2,X0))
    | sK0(sK2,sK3,k6_tmap_1(sK2,X0)) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_1216])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1034,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_1035,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_pre_topc(k6_tmap_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1034])).

cnf(c_1039,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_pre_topc(k6_tmap_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1035,c_20,c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1052,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_1053,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | l1_pre_topc(k6_tmap_1(sK2,X0))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1052])).

cnf(c_1057,plain,
    ( l1_pre_topc(k6_tmap_1(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1053,c_20,c_19])).

cnf(c_1058,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | l1_pre_topc(k6_tmap_1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_1057])).

cnf(c_1221,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,sK3,k6_tmap_1(sK2,X0)) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1217,c_20,c_19,c_1035,c_1053])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,X0_46)
    | sK0(sK2,sK3,k6_tmap_1(sK2,X0_46)) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_1221])).

cnf(c_2032,plain,
    ( k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,X0_46)
    | sK0(sK2,sK3,k6_tmap_1(sK2,X0_46)) = u1_struct_0(sK3)
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_3106,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3)
    | sK0(sK2,sK3,k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2012,c_2032])).

cnf(c_2332,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | sK0(sK2,sK3,k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_1395,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_2856,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k6_tmap_1(sK2,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1395])).

cnf(c_7,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_139,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_13])).

cnf(c_140,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_139])).

cnf(c_16,negated_conjecture,
    ( v1_tsep_1(sK3,sK2)
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_183,plain,
    ( v1_tsep_1(sK3,sK2)
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_505,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_140,c_183])).

cnf(c_506,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_508,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_19,c_17])).

cnf(c_1368,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_508])).

cnf(c_2008,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1368])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_974,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_975,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_974])).

cnf(c_979,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_975,c_20,c_19])).

cnf(c_1359,plain,
    ( ~ v3_pre_topc(X0_46,sK2)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X0_46) ),
    inference(subtyping,[status(esa)],[c_979])).

cnf(c_2021,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X0_46)
    | v3_pre_topc(X0_46,sK2) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1359])).

cnf(c_2519,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2012,c_2021])).

cnf(c_2677,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2008,c_2519])).

cnf(c_4,plain,
    ( ~ v3_pre_topc(sK1(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( ~ v1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_181,plain,
    ( ~ v1_tsep_1(sK3,sK2)
    | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(prop_impl,[status(thm)],[c_17,c_14])).

cnf(c_466,plain,
    ( ~ v3_pre_topc(sK1(X0,X1),X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_181])).

cnf(c_467,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_469,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_19,c_17])).

cnf(c_1371,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_469])).

cnf(c_2006,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_2966,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_2006])).

cnf(c_24,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_636,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_1426,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1395])).

cnf(c_1430,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_1432,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1368])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_995,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_996,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_995])).

cnf(c_1000,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_20,c_19])).

cnf(c_1358,plain,
    ( v3_pre_topc(X0_46,sK2)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X0_46) ),
    inference(subtyping,[status(esa)],[c_1000])).

cnf(c_2391,plain,
    ( v3_pre_topc(sK1(sK2,sK3),sK2)
    | ~ m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1358])).

cnf(c_2398,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK1(sK2,sK3))
    | v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2391])).

cnf(c_1406,plain,
    ( ~ m1_subset_1(X0_46,X0_47)
    | m1_subset_1(X1_46,X1_47)
    | X1_47 != X0_47
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_2367,plain,
    ( m1_subset_1(X0_46,X0_47)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | X0_47 != k1_zfmisc_1(u1_struct_0(sK2))
    | X0_46 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_2417,plain,
    ( m1_subset_1(sK1(sK2,sK3),X0_47)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | X0_47 != k1_zfmisc_1(u1_struct_0(sK2))
    | sK1(sK2,sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2367])).

cnf(c_2485,plain,
    ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK1(sK2,sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_2487,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK1(sK2,sK3) != u1_struct_0(sK3)
    | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2485])).

cnf(c_1394,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_2486,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_1408,plain,
    ( ~ v3_pre_topc(X0_46,X0_48)
    | v3_pre_topc(X1_46,X1_48)
    | X1_48 != X0_48
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_2379,plain,
    ( v3_pre_topc(X0_46,X0_48)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
    | X0_48 != sK2
    | X0_46 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1408])).

cnf(c_2496,plain,
    ( v3_pre_topc(sK1(sK2,sK3),X0_48)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
    | X0_48 != sK2
    | sK1(sK2,sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2379])).

cnf(c_2497,plain,
    ( X0_48 != sK2
    | sK1(sK2,sK3) != u1_struct_0(sK3)
    | v3_pre_topc(sK1(sK2,sK3),X0_48) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2496])).

cnf(c_2499,plain,
    ( sK2 != sK2
    | sK1(sK2,sK3) != u1_struct_0(sK3)
    | v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_2547,plain,
    ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1395])).

cnf(c_1398,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_2438,plain,
    ( X0_48 != X1_48
    | k8_tmap_1(sK2,sK3) != X1_48
    | k8_tmap_1(sK2,sK3) = X0_48 ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_2546,plain,
    ( X0_48 != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) = X0_48
    | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2438])).

cnf(c_2809,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_2696,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_48
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK1(sK2,sK3))
    | k6_tmap_1(sK2,sK1(sK2,sK3)) != X0_48 ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_2826,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK1(sK2,sK3))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | k6_tmap_1(sK2,sK1(sK2,sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2696])).

cnf(c_1401,plain,
    ( X0_48 != X1_48
    | k6_tmap_1(X0_48,X0_46) = k6_tmap_1(X1_48,X1_46)
    | X0_46 != X1_46 ),
    theory(equality)).

cnf(c_2744,plain,
    ( X0_48 != sK2
    | k6_tmap_1(X0_48,X0_46) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | X0_46 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_2917,plain,
    ( X0_48 != sK2
    | k6_tmap_1(X0_48,sK1(sK2,sK3)) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | sK1(sK2,sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2744])).

cnf(c_2918,plain,
    ( k6_tmap_1(sK2,sK1(sK2,sK3)) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | sK2 != sK2
    | sK1(sK2,sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2917])).

cnf(c_2786,plain,
    ( X0_48 != X1_48
    | X0_48 = k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) != X1_48 ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_2940,plain,
    ( X0_48 != k6_tmap_1(sK2,u1_struct_0(sK3))
    | X0_48 = k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) != k6_tmap_1(sK2,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2786])).

cnf(c_3030,plain,
    ( k6_tmap_1(X0_48,sK1(sK2,sK3)) != k6_tmap_1(sK2,u1_struct_0(sK3))
    | k6_tmap_1(X0_48,sK1(sK2,sK3)) = k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) != k6_tmap_1(sK2,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2940])).

cnf(c_3031,plain,
    ( k6_tmap_1(sK2,sK1(sK2,sK3)) != k6_tmap_1(sK2,u1_struct_0(sK3))
    | k6_tmap_1(sK2,sK1(sK2,sK3)) = k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) != k6_tmap_1(sK2,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3030])).

cnf(c_5,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_494,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK1(X1,X0) = u1_struct_0(X0)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_181])).

cnf(c_495,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_497,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_19,c_17])).

cnf(c_1369,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_497])).

cnf(c_2967,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2677,c_1369])).

cnf(c_3032,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2967,c_24,c_636,c_1426,c_1430,c_1369,c_1432,c_2398,c_2487,c_2486,c_2499,c_2547,c_2809,c_2826,c_2918,c_2966,c_3031])).

cnf(c_3037,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2966,c_24,c_636,c_1426,c_1430,c_1369,c_1432,c_2398,c_2487,c_2486,c_2499,c_2547,c_2809,c_2826,c_2918,c_2967,c_3031])).

cnf(c_3039,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3037])).

cnf(c_3041,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3037,c_24,c_636,c_1426,c_1430,c_1369,c_1432,c_2398,c_2487,c_2486,c_2499,c_2547,c_2809,c_2826,c_2918,c_2966,c_2967,c_3031])).

cnf(c_3061,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) != k6_tmap_1(sK2,u1_struct_0(sK3))
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) != k6_tmap_1(sK2,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2940])).

cnf(c_3173,plain,
    ( sK0(sK2,sK3,k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3106,c_19,c_24,c_635,c_636,c_1426,c_1430,c_1369,c_1432,c_2332,c_2398,c_2487,c_2486,c_2499,c_2547,c_2809,c_2826,c_2856,c_2918,c_2966,c_2967,c_3031,c_3061])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_672,plain,
    ( v2_struct_0(X0)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,sK0(X0,X2,X1)) != X1
    | k8_tmap_1(X0,X2) = X1
    | sK3 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_123])).

cnf(c_673,plain,
    ( v2_struct_0(sK2)
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_677,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_673,c_21,c_20,c_19])).

cnf(c_678,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK2,sK0(sK2,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_677])).

cnf(c_1195,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK2,X0) != X1
    | k6_tmap_1(sK2,sK0(sK2,sK3,X1)) != X1
    | k8_tmap_1(sK2,sK3) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_678,c_1021])).

cnf(c_1196,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(k6_tmap_1(sK2,X0))
    | ~ l1_pre_topc(k6_tmap_1(sK2,X0))
    | k6_tmap_1(sK2,sK0(sK2,sK3,k6_tmap_1(sK2,X0))) != k6_tmap_1(sK2,X0)
    | k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_1195])).

cnf(c_1200,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_tmap_1(sK2,sK0(sK2,sK3,k6_tmap_1(sK2,X0))) != k6_tmap_1(sK2,X0)
    | k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1196,c_20,c_19,c_1035,c_1053])).

cnf(c_1352,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_tmap_1(sK2,sK0(sK2,sK3,k6_tmap_1(sK2,X0_46))) != k6_tmap_1(sK2,X0_46)
    | k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,X0_46) ),
    inference(subtyping,[status(esa)],[c_1200])).

cnf(c_2031,plain,
    ( k6_tmap_1(sK2,sK0(sK2,sK3,k6_tmap_1(sK2,X0_46))) != k6_tmap_1(sK2,X0_46)
    | k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1352])).

cnf(c_3176,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3173,c_2031])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3176,c_3041,c_636,c_24])).


%------------------------------------------------------------------------------
