%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:04 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  243 (5415 expanded)
%              Number of clauses        :  160 (1261 expanded)
%              Number of leaves         :   17 (1214 expanded)
%              Depth                    :   24
%              Number of atoms          :  967 (43072 expanded)
%              Number of equality atoms :  257 (7427 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0,X1),X0)
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK0(X0,X1),X0)
                & u1_struct_0(X1) = sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK2)
          | ~ m1_pre_topc(sK2,X0)
          | ~ v1_tsep_1(sK2,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK2)
          | ( m1_pre_topc(sK2,X0)
            & v1_tsep_1(sK2,X0) ) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,X1)
            | ~ m1_pre_topc(X1,sK1)
            | ~ v1_tsep_1(X1,sK1) )
          & ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,X1)
            | ( m1_pre_topc(X1,sK1)
              & v1_tsep_1(X1,sK1) ) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | ~ v1_tsep_1(sK2,sK1) )
    & ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
      | ( m1_pre_topc(sK2,sK1)
        & v1_tsep_1(sK2,sK1) ) )
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f49,f51,f50])).

fof(f82,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
    | v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
    | m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f80,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m2_connsp_2(k2_struct_0(X0),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X0] :
      ( k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f53,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
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

fof(f69,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK0(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_210,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_23])).

cnf(c_211,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_26,negated_conjecture,
    ( v1_tsep_1(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_261,plain,
    ( v1_tsep_1(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_671,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_261])).

cnf(c_672,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_674,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_29,c_27])).

cnf(c_1321,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_674])).

cnf(c_2024,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
    | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_181,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_27])).

cnf(c_761,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_181])).

cnf(c_762,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_764,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_762,c_29])).

cnf(c_1316,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_764])).

cnf(c_2028,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1316])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1019,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_542,c_31])).

cnf(c_1020,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X0,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k5_tmap_1(sK1,X0) = u1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1019])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1024,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X0,sK1)
    | k5_tmap_1(sK1,X0) = u1_pre_topc(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1020,c_30,c_29])).

cnf(c_1304,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X0_50,sK1)
    | k5_tmap_1(sK1,X0_50) = u1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_1024])).

cnf(c_2045,plain,
    ( k5_tmap_1(sK1,X0_50) = u1_pre_topc(sK1)
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0_50,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1304])).

cnf(c_3165,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(sK1)
    | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2028,c_2045])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_193,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_23])).

cnf(c_194,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_753,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0))
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_181])).

cnf(c_754,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_756,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_754,c_31,c_30,c_29,c_28])).

cnf(c_1317,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_756])).

cnf(c_3168,plain,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) = u1_pre_topc(sK1)
    | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3165,c_1317])).

cnf(c_3216,plain,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) = u1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2024,c_3168])).

cnf(c_5,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6,plain,
    ( m2_connsp_2(k2_struct_0(X0),X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X2 != X0
    | k2_struct_0(X3) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_6])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_428,c_31])).

cnf(c_1062,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1061])).

cnf(c_1066,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_30,c_29])).

cnf(c_1302,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_1066])).

cnf(c_2047,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_34,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_763,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_2332,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_2333,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2332])).

cnf(c_2882,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2047,c_34,c_763,c_2333])).

cnf(c_3164,plain,
    ( k5_tmap_1(sK1,k2_struct_0(sK1)) = u1_pre_topc(sK1)
    | v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2882,c_2045])).

cnf(c_33,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2547,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(k2_struct_0(sK1),sK1)
    | k5_tmap_1(sK1,k2_struct_0(sK1)) = u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_2548,plain,
    ( k5_tmap_1(sK1,k2_struct_0(sK1)) = u1_pre_topc(sK1)
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2547])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(k1_tops_1(X1,X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1328,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_52)))
    | v3_pre_topc(k1_tops_1(X0_52,X0_50),X0_52)
    | ~ v2_pre_topc(X0_52)
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2018,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | v3_pre_topc(k1_tops_1(X0_52,X0_50),X0_52) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_2890,plain,
    ( v3_pre_topc(k1_tops_1(sK1,k2_struct_0(sK1)),sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2882,c_2018])).

cnf(c_1325,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2021,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1325])).

cnf(c_4,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1327,plain,
    ( ~ v2_pre_topc(X0_52)
    | ~ l1_pre_topc(X0_52)
    | k1_tops_1(X0_52,k2_struct_0(X0_52)) = k2_struct_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2019,plain,
    ( k1_tops_1(X0_52,k2_struct_0(X0_52)) = k2_struct_0(X0_52)
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1327])).

cnf(c_2377,plain,
    ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2021,c_2019])).

cnf(c_1390,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_2430,plain,
    ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2377,c_30,c_29,c_1390])).

cnf(c_2894,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2890,c_2430])).

cnf(c_4050,plain,
    ( k5_tmap_1(sK1,k2_struct_0(sK1)) = u1_pre_topc(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3164,c_33,c_34,c_763,c_2333,c_2548,c_2894])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1097,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_1098,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_1097])).

cnf(c_1102,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1098,c_30,c_29])).

cnf(c_1300,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(sK1,X0_50)) = k5_tmap_1(sK1,X0_50) ),
    inference(subtyping,[status(esa)],[c_1102])).

cnf(c_2049,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,X0_50)) = k5_tmap_1(sK1,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1300])).

cnf(c_2910,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,k2_struct_0(sK1))) = k5_tmap_1(sK1,k2_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_2882,c_2049])).

cnf(c_4053,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,k2_struct_0(sK1))) = u1_pre_topc(sK1) ),
    inference(demodulation,[status(thm)],[c_4050,c_2910])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1115,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_1116,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_1115])).

cnf(c_1120,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1116,c_30,c_29])).

cnf(c_1269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK1,X0) != X1
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1120])).

cnf(c_1270,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK1,X0))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_1269])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1151,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_1152,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1151])).

cnf(c_1274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1270,c_30,c_29,c_1152])).

cnf(c_1296,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0_50)),u1_pre_topc(k6_tmap_1(sK1,X0_50))) = k6_tmap_1(sK1,X0_50) ),
    inference(subtyping,[status(esa)],[c_1274])).

cnf(c_2054,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0_50)),u1_pre_topc(k6_tmap_1(sK1,X0_50))) = k6_tmap_1(sK1,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_3660,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,k2_struct_0(sK1))),u1_pre_topc(k6_tmap_1(sK1,k2_struct_0(sK1)))) = k6_tmap_1(sK1,k2_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_2882,c_2054])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1079,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_1080,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1079])).

cnf(c_1084,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1080,c_30,c_29])).

cnf(c_1301,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0_50)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1084])).

cnf(c_2048,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0_50)) = u1_struct_0(sK1)
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1301])).

cnf(c_2887,plain,
    ( u1_struct_0(k6_tmap_1(sK1,k2_struct_0(sK1))) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2882,c_2048])).

cnf(c_4289,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k6_tmap_1(sK1,k2_struct_0(sK1)))) = k6_tmap_1(sK1,k2_struct_0(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_3660,c_2887])).

cnf(c_5082,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,k2_struct_0(sK1)) ),
    inference(demodulation,[status(thm)],[c_4053,c_4289])).

cnf(c_5147,plain,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) = u1_pre_topc(sK1)
    | k6_tmap_1(sK1,k2_struct_0(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3216,c_5082])).

cnf(c_5192,plain,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) = u1_pre_topc(sK1) ),
    inference(superposition,[status(thm)],[c_5147,c_4053])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_780,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_181])).

cnf(c_781,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_783,plain,
    ( v1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_781,c_31,c_30,c_29])).

cnf(c_1237,plain,
    ( ~ l1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) != X0
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_783])).

cnf(c_1238,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1237])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_802,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_181])).

cnf(c_803,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_855,plain,
    ( ~ l1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) != X0
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_783])).

cnf(c_856,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_855])).

cnf(c_1240,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1238,c_31,c_30,c_29,c_803,c_856])).

cnf(c_1312,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_1240])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_772,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_181])).

cnf(c_773,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_775,plain,
    ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_773,c_31,c_30,c_29,c_28])).

cnf(c_1315,plain,
    ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_775])).

cnf(c_2073,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1312,c_1315])).

cnf(c_5298,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_5192,c_2073])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_597,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_211])).

cnf(c_725,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_597,c_181])).

cnf(c_726,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_728,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_726,c_29])).

cnf(c_1319,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_728])).

cnf(c_2026,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2)
    | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_3314,plain,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) = u1_pre_topc(sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2026,c_3168])).

cnf(c_4294,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3314,c_2073])).

cnf(c_24,negated_conjecture,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_259,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(prop_impl,[status(thm)],[c_27,c_24])).

cnf(c_646,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_259])).

cnf(c_647,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_649,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_29,c_27])).

cnf(c_1323,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_649])).

cnf(c_4426,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4294,c_1323])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_657,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_259])).

cnf(c_658,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v3_pre_topc(sK0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_660,plain,
    ( ~ v3_pre_topc(sK0(sK1,sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_658,c_29,c_27])).

cnf(c_1322,plain,
    ( ~ v3_pre_topc(sK0(sK1,sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_660])).

cnf(c_2023,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | v3_pre_topc(sK0(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_4434,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4426,c_2023])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_17,c_1])).

cnf(c_1040,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_519,c_31])).

cnf(c_1041,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(X0,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k5_tmap_1(sK1,X0) != u1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1040])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(X0,sK1)
    | k5_tmap_1(sK1,X0) != u1_pre_topc(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1041,c_30,c_29])).

cnf(c_1303,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(X0_50,sK1)
    | k5_tmap_1(sK1,X0_50) != u1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_1045])).

cnf(c_2046,plain,
    ( k5_tmap_1(sK1,X0_50) != u1_pre_topc(sK1)
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0_50,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1303])).

cnf(c_3211,plain,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) != u1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_2046])).

cnf(c_3278,plain,
    ( u1_pre_topc(k8_tmap_1(sK1,sK2)) != u1_pre_topc(sK1)
    | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3211,c_34,c_763])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5298,c_5192,c_4434,c_3278])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.83/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/0.99  
% 2.83/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.83/0.99  
% 2.83/0.99  ------  iProver source info
% 2.83/0.99  
% 2.83/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.83/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.83/0.99  git: non_committed_changes: false
% 2.83/0.99  git: last_make_outside_of_git: false
% 2.83/0.99  
% 2.83/0.99  ------ 
% 2.83/0.99  
% 2.83/0.99  ------ Input Options
% 2.83/0.99  
% 2.83/0.99  --out_options                           all
% 2.83/0.99  --tptp_safe_out                         true
% 2.83/0.99  --problem_path                          ""
% 2.83/0.99  --include_path                          ""
% 2.83/0.99  --clausifier                            res/vclausify_rel
% 2.83/0.99  --clausifier_options                    --mode clausify
% 2.83/0.99  --stdin                                 false
% 2.83/0.99  --stats_out                             all
% 2.83/0.99  
% 2.83/0.99  ------ General Options
% 2.83/0.99  
% 2.83/0.99  --fof                                   false
% 2.83/0.99  --time_out_real                         305.
% 2.83/0.99  --time_out_virtual                      -1.
% 2.83/0.99  --symbol_type_check                     false
% 2.83/0.99  --clausify_out                          false
% 2.83/0.99  --sig_cnt_out                           false
% 2.83/0.99  --trig_cnt_out                          false
% 2.83/0.99  --trig_cnt_out_tolerance                1.
% 2.83/0.99  --trig_cnt_out_sk_spl                   false
% 2.83/0.99  --abstr_cl_out                          false
% 2.83/0.99  
% 2.83/0.99  ------ Global Options
% 2.83/0.99  
% 2.83/0.99  --schedule                              default
% 2.83/0.99  --add_important_lit                     false
% 2.83/0.99  --prop_solver_per_cl                    1000
% 2.83/0.99  --min_unsat_core                        false
% 2.83/0.99  --soft_assumptions                      false
% 2.83/0.99  --soft_lemma_size                       3
% 2.83/0.99  --prop_impl_unit_size                   0
% 2.83/0.99  --prop_impl_unit                        []
% 2.83/0.99  --share_sel_clauses                     true
% 2.83/0.99  --reset_solvers                         false
% 2.83/0.99  --bc_imp_inh                            [conj_cone]
% 2.83/0.99  --conj_cone_tolerance                   3.
% 2.83/0.99  --extra_neg_conj                        none
% 2.83/0.99  --large_theory_mode                     true
% 2.83/0.99  --prolific_symb_bound                   200
% 2.83/0.99  --lt_threshold                          2000
% 2.83/0.99  --clause_weak_htbl                      true
% 2.83/0.99  --gc_record_bc_elim                     false
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing Options
% 2.83/0.99  
% 2.83/0.99  --preprocessing_flag                    true
% 2.83/0.99  --time_out_prep_mult                    0.1
% 2.83/0.99  --splitting_mode                        input
% 2.83/0.99  --splitting_grd                         true
% 2.83/0.99  --splitting_cvd                         false
% 2.83/0.99  --splitting_cvd_svl                     false
% 2.83/0.99  --splitting_nvd                         32
% 2.83/0.99  --sub_typing                            true
% 2.83/0.99  --prep_gs_sim                           true
% 2.83/0.99  --prep_unflatten                        true
% 2.83/0.99  --prep_res_sim                          true
% 2.83/0.99  --prep_upred                            true
% 2.83/0.99  --prep_sem_filter                       exhaustive
% 2.83/0.99  --prep_sem_filter_out                   false
% 2.83/0.99  --pred_elim                             true
% 2.83/0.99  --res_sim_input                         true
% 2.83/0.99  --eq_ax_congr_red                       true
% 2.83/0.99  --pure_diseq_elim                       true
% 2.83/0.99  --brand_transform                       false
% 2.83/0.99  --non_eq_to_eq                          false
% 2.83/0.99  --prep_def_merge                        true
% 2.83/0.99  --prep_def_merge_prop_impl              false
% 2.83/0.99  --prep_def_merge_mbd                    true
% 2.83/0.99  --prep_def_merge_tr_red                 false
% 2.83/0.99  --prep_def_merge_tr_cl                  false
% 2.83/0.99  --smt_preprocessing                     true
% 2.83/0.99  --smt_ac_axioms                         fast
% 2.83/0.99  --preprocessed_out                      false
% 2.83/0.99  --preprocessed_stats                    false
% 2.83/0.99  
% 2.83/0.99  ------ Abstraction refinement Options
% 2.83/0.99  
% 2.83/0.99  --abstr_ref                             []
% 2.83/0.99  --abstr_ref_prep                        false
% 2.83/0.99  --abstr_ref_until_sat                   false
% 2.83/0.99  --abstr_ref_sig_restrict                funpre
% 2.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.83/0.99  --abstr_ref_under                       []
% 2.83/0.99  
% 2.83/0.99  ------ SAT Options
% 2.83/0.99  
% 2.83/0.99  --sat_mode                              false
% 2.83/0.99  --sat_fm_restart_options                ""
% 2.83/0.99  --sat_gr_def                            false
% 2.83/0.99  --sat_epr_types                         true
% 2.83/0.99  --sat_non_cyclic_types                  false
% 2.83/0.99  --sat_finite_models                     false
% 2.83/0.99  --sat_fm_lemmas                         false
% 2.83/0.99  --sat_fm_prep                           false
% 2.83/0.99  --sat_fm_uc_incr                        true
% 2.83/0.99  --sat_out_model                         small
% 2.83/0.99  --sat_out_clauses                       false
% 2.83/0.99  
% 2.83/0.99  ------ QBF Options
% 2.83/0.99  
% 2.83/0.99  --qbf_mode                              false
% 2.83/0.99  --qbf_elim_univ                         false
% 2.83/0.99  --qbf_dom_inst                          none
% 2.83/0.99  --qbf_dom_pre_inst                      false
% 2.83/0.99  --qbf_sk_in                             false
% 2.83/0.99  --qbf_pred_elim                         true
% 2.83/0.99  --qbf_split                             512
% 2.83/0.99  
% 2.83/0.99  ------ BMC1 Options
% 2.83/0.99  
% 2.83/0.99  --bmc1_incremental                      false
% 2.83/0.99  --bmc1_axioms                           reachable_all
% 2.83/0.99  --bmc1_min_bound                        0
% 2.83/0.99  --bmc1_max_bound                        -1
% 2.83/0.99  --bmc1_max_bound_default                -1
% 2.83/0.99  --bmc1_symbol_reachability              true
% 2.83/0.99  --bmc1_property_lemmas                  false
% 2.83/0.99  --bmc1_k_induction                      false
% 2.83/0.99  --bmc1_non_equiv_states                 false
% 2.83/0.99  --bmc1_deadlock                         false
% 2.83/0.99  --bmc1_ucm                              false
% 2.83/0.99  --bmc1_add_unsat_core                   none
% 2.83/0.99  --bmc1_unsat_core_children              false
% 2.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.83/0.99  --bmc1_out_stat                         full
% 2.83/0.99  --bmc1_ground_init                      false
% 2.83/0.99  --bmc1_pre_inst_next_state              false
% 2.83/0.99  --bmc1_pre_inst_state                   false
% 2.83/0.99  --bmc1_pre_inst_reach_state             false
% 2.83/0.99  --bmc1_out_unsat_core                   false
% 2.83/0.99  --bmc1_aig_witness_out                  false
% 2.83/0.99  --bmc1_verbose                          false
% 2.83/0.99  --bmc1_dump_clauses_tptp                false
% 2.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.83/0.99  --bmc1_dump_file                        -
% 2.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.83/0.99  --bmc1_ucm_extend_mode                  1
% 2.83/0.99  --bmc1_ucm_init_mode                    2
% 2.83/0.99  --bmc1_ucm_cone_mode                    none
% 2.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.83/0.99  --bmc1_ucm_relax_model                  4
% 2.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.83/0.99  --bmc1_ucm_layered_model                none
% 2.83/0.99  --bmc1_ucm_max_lemma_size               10
% 2.83/0.99  
% 2.83/0.99  ------ AIG Options
% 2.83/0.99  
% 2.83/0.99  --aig_mode                              false
% 2.83/0.99  
% 2.83/0.99  ------ Instantiation Options
% 2.83/0.99  
% 2.83/0.99  --instantiation_flag                    true
% 2.83/0.99  --inst_sos_flag                         false
% 2.83/0.99  --inst_sos_phase                        true
% 2.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.83/0.99  --inst_lit_sel_side                     num_symb
% 2.83/0.99  --inst_solver_per_active                1400
% 2.83/0.99  --inst_solver_calls_frac                1.
% 2.83/0.99  --inst_passive_queue_type               priority_queues
% 2.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.83/0.99  --inst_passive_queues_freq              [25;2]
% 2.83/0.99  --inst_dismatching                      true
% 2.83/0.99  --inst_eager_unprocessed_to_passive     true
% 2.83/0.99  --inst_prop_sim_given                   true
% 2.83/0.99  --inst_prop_sim_new                     false
% 2.83/0.99  --inst_subs_new                         false
% 2.83/0.99  --inst_eq_res_simp                      false
% 2.83/0.99  --inst_subs_given                       false
% 2.83/0.99  --inst_orphan_elimination               true
% 2.83/0.99  --inst_learning_loop_flag               true
% 2.83/0.99  --inst_learning_start                   3000
% 2.83/0.99  --inst_learning_factor                  2
% 2.83/0.99  --inst_start_prop_sim_after_learn       3
% 2.83/0.99  --inst_sel_renew                        solver
% 2.83/0.99  --inst_lit_activity_flag                true
% 2.83/0.99  --inst_restr_to_given                   false
% 2.83/0.99  --inst_activity_threshold               500
% 2.83/0.99  --inst_out_proof                        true
% 2.83/0.99  
% 2.83/0.99  ------ Resolution Options
% 2.83/0.99  
% 2.83/0.99  --resolution_flag                       true
% 2.83/0.99  --res_lit_sel                           adaptive
% 2.83/0.99  --res_lit_sel_side                      none
% 2.83/0.99  --res_ordering                          kbo
% 2.83/0.99  --res_to_prop_solver                    active
% 2.83/0.99  --res_prop_simpl_new                    false
% 2.83/0.99  --res_prop_simpl_given                  true
% 2.83/0.99  --res_passive_queue_type                priority_queues
% 2.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.83/0.99  --res_passive_queues_freq               [15;5]
% 2.83/0.99  --res_forward_subs                      full
% 2.83/0.99  --res_backward_subs                     full
% 2.83/0.99  --res_forward_subs_resolution           true
% 2.83/0.99  --res_backward_subs_resolution          true
% 2.83/0.99  --res_orphan_elimination                true
% 2.83/0.99  --res_time_limit                        2.
% 2.83/0.99  --res_out_proof                         true
% 2.83/0.99  
% 2.83/0.99  ------ Superposition Options
% 2.83/0.99  
% 2.83/0.99  --superposition_flag                    true
% 2.83/0.99  --sup_passive_queue_type                priority_queues
% 2.83/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.83/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.83/0.99  --demod_completeness_check              fast
% 2.83/0.99  --demod_use_ground                      true
% 2.83/0.99  --sup_to_prop_solver                    passive
% 2.83/0.99  --sup_prop_simpl_new                    true
% 2.83/0.99  --sup_prop_simpl_given                  true
% 2.83/0.99  --sup_fun_splitting                     false
% 2.83/0.99  --sup_smt_interval                      50000
% 2.83/0.99  
% 2.83/0.99  ------ Superposition Simplification Setup
% 2.83/0.99  
% 2.83/0.99  --sup_indices_passive                   []
% 2.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_full_bw                           [BwDemod]
% 2.83/0.99  --sup_immed_triv                        [TrivRules]
% 2.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_immed_bw_main                     []
% 2.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.83/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/1.00  
% 2.83/1.00  ------ Combination Options
% 2.83/1.00  
% 2.83/1.00  --comb_res_mult                         3
% 2.83/1.00  --comb_sup_mult                         2
% 2.83/1.00  --comb_inst_mult                        10
% 2.83/1.00  
% 2.83/1.00  ------ Debug Options
% 2.83/1.00  
% 2.83/1.00  --dbg_backtrace                         false
% 2.83/1.00  --dbg_dump_prop_clauses                 false
% 2.83/1.00  --dbg_dump_prop_clauses_file            -
% 2.83/1.00  --dbg_out_stat                          false
% 2.83/1.00  ------ Parsing...
% 2.83/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.83/1.00  
% 2.83/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 2.83/1.00  
% 2.83/1.00  ------ Preprocessing... gs_s  sp: 8 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.83/1.00  
% 2.83/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.83/1.00  ------ Proving...
% 2.83/1.00  ------ Problem Properties 
% 2.83/1.00  
% 2.83/1.00  
% 2.83/1.00  clauses                                 41
% 2.83/1.00  conjectures                             2
% 2.83/1.00  EPR                                     9
% 2.83/1.00  Horn                                    37
% 2.83/1.00  unary                                   8
% 2.83/1.00  binary                                  14
% 2.83/1.00  lits                                    97
% 2.83/1.00  lits eq                                 20
% 2.83/1.00  fd_pure                                 0
% 2.83/1.00  fd_pseudo                               0
% 2.83/1.00  fd_cond                                 0
% 2.83/1.00  fd_pseudo_cond                          0
% 2.83/1.00  AC symbols                              0
% 2.83/1.00  
% 2.83/1.00  ------ Schedule dynamic 5 is on 
% 2.83/1.00  
% 2.83/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.83/1.00  
% 2.83/1.00  
% 2.83/1.00  ------ 
% 2.83/1.00  Current options:
% 2.83/1.00  ------ 
% 2.83/1.00  
% 2.83/1.00  ------ Input Options
% 2.83/1.00  
% 2.83/1.00  --out_options                           all
% 2.83/1.00  --tptp_safe_out                         true
% 2.83/1.00  --problem_path                          ""
% 2.83/1.00  --include_path                          ""
% 2.83/1.00  --clausifier                            res/vclausify_rel
% 2.83/1.00  --clausifier_options                    --mode clausify
% 2.83/1.00  --stdin                                 false
% 2.83/1.00  --stats_out                             all
% 2.83/1.00  
% 2.83/1.00  ------ General Options
% 2.83/1.00  
% 2.83/1.00  --fof                                   false
% 2.83/1.00  --time_out_real                         305.
% 2.83/1.00  --time_out_virtual                      -1.
% 2.83/1.00  --symbol_type_check                     false
% 2.83/1.00  --clausify_out                          false
% 2.83/1.00  --sig_cnt_out                           false
% 2.83/1.00  --trig_cnt_out                          false
% 2.83/1.00  --trig_cnt_out_tolerance                1.
% 2.83/1.00  --trig_cnt_out_sk_spl                   false
% 2.83/1.00  --abstr_cl_out                          false
% 2.83/1.00  
% 2.83/1.00  ------ Global Options
% 2.83/1.00  
% 2.83/1.00  --schedule                              default
% 2.83/1.00  --add_important_lit                     false
% 2.83/1.00  --prop_solver_per_cl                    1000
% 2.83/1.00  --min_unsat_core                        false
% 2.83/1.00  --soft_assumptions                      false
% 2.83/1.00  --soft_lemma_size                       3
% 2.83/1.00  --prop_impl_unit_size                   0
% 2.83/1.00  --prop_impl_unit                        []
% 2.83/1.00  --share_sel_clauses                     true
% 2.83/1.00  --reset_solvers                         false
% 2.83/1.00  --bc_imp_inh                            [conj_cone]
% 2.83/1.00  --conj_cone_tolerance                   3.
% 2.83/1.00  --extra_neg_conj                        none
% 2.83/1.00  --large_theory_mode                     true
% 2.83/1.00  --prolific_symb_bound                   200
% 2.83/1.00  --lt_threshold                          2000
% 2.83/1.00  --clause_weak_htbl                      true
% 2.83/1.00  --gc_record_bc_elim                     false
% 2.83/1.00  
% 2.83/1.00  ------ Preprocessing Options
% 2.83/1.00  
% 2.83/1.00  --preprocessing_flag                    true
% 2.83/1.00  --time_out_prep_mult                    0.1
% 2.83/1.00  --splitting_mode                        input
% 2.83/1.00  --splitting_grd                         true
% 2.83/1.00  --splitting_cvd                         false
% 2.83/1.00  --splitting_cvd_svl                     false
% 2.83/1.00  --splitting_nvd                         32
% 2.83/1.00  --sub_typing                            true
% 2.83/1.00  --prep_gs_sim                           true
% 2.83/1.00  --prep_unflatten                        true
% 2.83/1.00  --prep_res_sim                          true
% 2.83/1.00  --prep_upred                            true
% 2.83/1.00  --prep_sem_filter                       exhaustive
% 2.83/1.00  --prep_sem_filter_out                   false
% 2.83/1.00  --pred_elim                             true
% 2.83/1.00  --res_sim_input                         true
% 2.83/1.00  --eq_ax_congr_red                       true
% 2.83/1.00  --pure_diseq_elim                       true
% 2.83/1.00  --brand_transform                       false
% 2.83/1.00  --non_eq_to_eq                          false
% 2.83/1.00  --prep_def_merge                        true
% 2.83/1.00  --prep_def_merge_prop_impl              false
% 2.83/1.00  --prep_def_merge_mbd                    true
% 2.83/1.00  --prep_def_merge_tr_red                 false
% 2.83/1.00  --prep_def_merge_tr_cl                  false
% 2.83/1.00  --smt_preprocessing                     true
% 2.83/1.00  --smt_ac_axioms                         fast
% 2.83/1.00  --preprocessed_out                      false
% 2.83/1.00  --preprocessed_stats                    false
% 2.83/1.00  
% 2.83/1.00  ------ Abstraction refinement Options
% 2.83/1.00  
% 2.83/1.00  --abstr_ref                             []
% 2.83/1.00  --abstr_ref_prep                        false
% 2.83/1.00  --abstr_ref_until_sat                   false
% 2.83/1.00  --abstr_ref_sig_restrict                funpre
% 2.83/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.83/1.00  --abstr_ref_under                       []
% 2.83/1.00  
% 2.83/1.00  ------ SAT Options
% 2.83/1.00  
% 2.83/1.00  --sat_mode                              false
% 2.83/1.00  --sat_fm_restart_options                ""
% 2.83/1.00  --sat_gr_def                            false
% 2.83/1.00  --sat_epr_types                         true
% 2.83/1.00  --sat_non_cyclic_types                  false
% 2.83/1.00  --sat_finite_models                     false
% 2.83/1.00  --sat_fm_lemmas                         false
% 2.83/1.00  --sat_fm_prep                           false
% 2.83/1.00  --sat_fm_uc_incr                        true
% 2.83/1.00  --sat_out_model                         small
% 2.83/1.00  --sat_out_clauses                       false
% 2.83/1.00  
% 2.83/1.00  ------ QBF Options
% 2.83/1.00  
% 2.83/1.00  --qbf_mode                              false
% 2.83/1.00  --qbf_elim_univ                         false
% 2.83/1.00  --qbf_dom_inst                          none
% 2.83/1.00  --qbf_dom_pre_inst                      false
% 2.83/1.00  --qbf_sk_in                             false
% 2.83/1.00  --qbf_pred_elim                         true
% 2.83/1.00  --qbf_split                             512
% 2.83/1.00  
% 2.83/1.00  ------ BMC1 Options
% 2.83/1.00  
% 2.83/1.00  --bmc1_incremental                      false
% 2.83/1.00  --bmc1_axioms                           reachable_all
% 2.83/1.00  --bmc1_min_bound                        0
% 2.83/1.00  --bmc1_max_bound                        -1
% 2.83/1.00  --bmc1_max_bound_default                -1
% 2.83/1.00  --bmc1_symbol_reachability              true
% 2.83/1.00  --bmc1_property_lemmas                  false
% 2.83/1.00  --bmc1_k_induction                      false
% 2.83/1.00  --bmc1_non_equiv_states                 false
% 2.83/1.00  --bmc1_deadlock                         false
% 2.83/1.00  --bmc1_ucm                              false
% 2.83/1.00  --bmc1_add_unsat_core                   none
% 2.83/1.00  --bmc1_unsat_core_children              false
% 2.83/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.83/1.00  --bmc1_out_stat                         full
% 2.83/1.00  --bmc1_ground_init                      false
% 2.83/1.00  --bmc1_pre_inst_next_state              false
% 2.83/1.00  --bmc1_pre_inst_state                   false
% 2.83/1.00  --bmc1_pre_inst_reach_state             false
% 2.83/1.00  --bmc1_out_unsat_core                   false
% 2.83/1.00  --bmc1_aig_witness_out                  false
% 2.83/1.00  --bmc1_verbose                          false
% 2.83/1.00  --bmc1_dump_clauses_tptp                false
% 2.83/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.83/1.00  --bmc1_dump_file                        -
% 2.83/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.83/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.83/1.00  --bmc1_ucm_extend_mode                  1
% 2.83/1.00  --bmc1_ucm_init_mode                    2
% 2.83/1.00  --bmc1_ucm_cone_mode                    none
% 2.83/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.83/1.00  --bmc1_ucm_relax_model                  4
% 2.83/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.83/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.83/1.00  --bmc1_ucm_layered_model                none
% 2.83/1.00  --bmc1_ucm_max_lemma_size               10
% 2.83/1.00  
% 2.83/1.00  ------ AIG Options
% 2.83/1.00  
% 2.83/1.00  --aig_mode                              false
% 2.83/1.00  
% 2.83/1.00  ------ Instantiation Options
% 2.83/1.00  
% 2.83/1.00  --instantiation_flag                    true
% 2.83/1.00  --inst_sos_flag                         false
% 2.83/1.00  --inst_sos_phase                        true
% 2.83/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.83/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.83/1.00  --inst_lit_sel_side                     none
% 2.83/1.00  --inst_solver_per_active                1400
% 2.83/1.00  --inst_solver_calls_frac                1.
% 2.83/1.00  --inst_passive_queue_type               priority_queues
% 2.83/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.83/1.00  --inst_passive_queues_freq              [25;2]
% 2.83/1.00  --inst_dismatching                      true
% 2.83/1.00  --inst_eager_unprocessed_to_passive     true
% 2.83/1.00  --inst_prop_sim_given                   true
% 2.83/1.00  --inst_prop_sim_new                     false
% 2.83/1.00  --inst_subs_new                         false
% 2.83/1.00  --inst_eq_res_simp                      false
% 2.83/1.00  --inst_subs_given                       false
% 2.83/1.00  --inst_orphan_elimination               true
% 2.83/1.00  --inst_learning_loop_flag               true
% 2.83/1.00  --inst_learning_start                   3000
% 2.83/1.00  --inst_learning_factor                  2
% 2.83/1.00  --inst_start_prop_sim_after_learn       3
% 2.83/1.00  --inst_sel_renew                        solver
% 2.83/1.00  --inst_lit_activity_flag                true
% 2.83/1.00  --inst_restr_to_given                   false
% 2.83/1.00  --inst_activity_threshold               500
% 2.83/1.00  --inst_out_proof                        true
% 2.83/1.00  
% 2.83/1.00  ------ Resolution Options
% 2.83/1.00  
% 2.83/1.00  --resolution_flag                       false
% 2.83/1.00  --res_lit_sel                           adaptive
% 2.83/1.00  --res_lit_sel_side                      none
% 2.83/1.00  --res_ordering                          kbo
% 2.83/1.00  --res_to_prop_solver                    active
% 2.83/1.00  --res_prop_simpl_new                    false
% 2.83/1.00  --res_prop_simpl_given                  true
% 2.83/1.00  --res_passive_queue_type                priority_queues
% 2.83/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.83/1.00  --res_passive_queues_freq               [15;5]
% 2.83/1.00  --res_forward_subs                      full
% 2.83/1.00  --res_backward_subs                     full
% 2.83/1.00  --res_forward_subs_resolution           true
% 2.83/1.00  --res_backward_subs_resolution          true
% 2.83/1.00  --res_orphan_elimination                true
% 2.83/1.00  --res_time_limit                        2.
% 2.83/1.00  --res_out_proof                         true
% 2.83/1.00  
% 2.83/1.00  ------ Superposition Options
% 2.83/1.00  
% 2.83/1.00  --superposition_flag                    true
% 2.83/1.00  --sup_passive_queue_type                priority_queues
% 2.83/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.83/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.83/1.00  --demod_completeness_check              fast
% 2.83/1.00  --demod_use_ground                      true
% 2.83/1.00  --sup_to_prop_solver                    passive
% 2.83/1.00  --sup_prop_simpl_new                    true
% 2.83/1.00  --sup_prop_simpl_given                  true
% 2.83/1.00  --sup_fun_splitting                     false
% 2.83/1.00  --sup_smt_interval                      50000
% 2.83/1.00  
% 2.83/1.00  ------ Superposition Simplification Setup
% 2.83/1.00  
% 2.83/1.00  --sup_indices_passive                   []
% 2.83/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.83/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.00  --sup_full_bw                           [BwDemod]
% 2.83/1.00  --sup_immed_triv                        [TrivRules]
% 2.83/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.83/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.00  --sup_immed_bw_main                     []
% 2.83/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.83/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/1.00  
% 2.83/1.00  ------ Combination Options
% 2.83/1.00  
% 2.83/1.00  --comb_res_mult                         3
% 2.83/1.00  --comb_sup_mult                         2
% 2.83/1.00  --comb_inst_mult                        10
% 2.83/1.00  
% 2.83/1.00  ------ Debug Options
% 2.83/1.00  
% 2.83/1.00  --dbg_backtrace                         false
% 2.83/1.00  --dbg_dump_prop_clauses                 false
% 2.83/1.00  --dbg_dump_prop_clauses_file            -
% 2.83/1.00  --dbg_out_stat                          false
% 2.83/1.00  
% 2.83/1.00  
% 2.83/1.00  
% 2.83/1.00  
% 2.83/1.00  ------ Proving...
% 2.83/1.00  
% 2.83/1.00  
% 2.83/1.00  % SZS status Theorem for theBenchmark.p
% 2.83/1.00  
% 2.83/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.83/1.00  
% 2.83/1.00  fof(f7,axiom,(
% 2.83/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f27,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.83/1.00    inference(ennf_transformation,[],[f7])).
% 2.83/1.00  
% 2.83/1.00  fof(f28,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.83/1.00    inference(flattening,[],[f27])).
% 2.83/1.00  
% 2.83/1.00  fof(f43,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.83/1.00    inference(nnf_transformation,[],[f28])).
% 2.83/1.00  
% 2.83/1.00  fof(f44,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.83/1.00    inference(rectify,[],[f43])).
% 2.83/1.00  
% 2.83/1.00  fof(f45,plain,(
% 2.83/1.00    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.83/1.00    introduced(choice_axiom,[])).
% 2.83/1.00  
% 2.83/1.00  fof(f46,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.83/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 2.83/1.00  
% 2.83/1.00  fof(f60,plain,(
% 2.83/1.00    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f46])).
% 2.83/1.00  
% 2.83/1.00  fof(f85,plain,(
% 2.83/1.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.83/1.00    inference(equality_resolution,[],[f60])).
% 2.83/1.00  
% 2.83/1.00  fof(f13,axiom,(
% 2.83/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f39,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.83/1.00    inference(ennf_transformation,[],[f13])).
% 2.83/1.00  
% 2.83/1.00  fof(f76,plain,(
% 2.83/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f39])).
% 2.83/1.00  
% 2.83/1.00  fof(f14,conjecture,(
% 2.83/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f15,negated_conjecture,(
% 2.83/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 2.83/1.00    inference(negated_conjecture,[],[f14])).
% 2.83/1.00  
% 2.83/1.00  fof(f40,plain,(
% 2.83/1.00    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.83/1.00    inference(ennf_transformation,[],[f15])).
% 2.83/1.00  
% 2.83/1.00  fof(f41,plain,(
% 2.83/1.00    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.83/1.00    inference(flattening,[],[f40])).
% 2.83/1.00  
% 2.83/1.00  fof(f48,plain,(
% 2.83/1.00    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.83/1.00    inference(nnf_transformation,[],[f41])).
% 2.83/1.00  
% 2.83/1.00  fof(f49,plain,(
% 2.83/1.00    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.83/1.00    inference(flattening,[],[f48])).
% 2.83/1.00  
% 2.83/1.00  fof(f51,plain,(
% 2.83/1.00    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK2) | ~m1_pre_topc(sK2,X0) | ~v1_tsep_1(sK2,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK2) | (m1_pre_topc(sK2,X0) & v1_tsep_1(sK2,X0))) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.83/1.00    introduced(choice_axiom,[])).
% 2.83/1.00  
% 2.83/1.00  fof(f50,plain,(
% 2.83/1.00    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,X1) | ~m1_pre_topc(X1,sK1) | ~v1_tsep_1(X1,sK1)) & (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,X1) | (m1_pre_topc(X1,sK1) & v1_tsep_1(X1,sK1))) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.83/1.00    introduced(choice_axiom,[])).
% 2.83/1.00  
% 2.83/1.00  fof(f52,plain,(
% 2.83/1.00    ((g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)) & (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) | (m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1))) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.83/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f49,f51,f50])).
% 2.83/1.00  
% 2.83/1.00  fof(f82,plain,(
% 2.83/1.00    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) | v1_tsep_1(sK2,sK1)),
% 2.83/1.00    inference(cnf_transformation,[],[f52])).
% 2.83/1.00  
% 2.83/1.00  fof(f79,plain,(
% 2.83/1.00    l1_pre_topc(sK1)),
% 2.83/1.00    inference(cnf_transformation,[],[f52])).
% 2.83/1.00  
% 2.83/1.00  fof(f81,plain,(
% 2.83/1.00    m1_pre_topc(sK2,sK1)),
% 2.83/1.00    inference(cnf_transformation,[],[f52])).
% 2.83/1.00  
% 2.83/1.00  fof(f83,plain,(
% 2.83/1.00    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) | m1_pre_topc(sK2,sK1)),
% 2.83/1.00    inference(cnf_transformation,[],[f52])).
% 2.83/1.00  
% 2.83/1.00  fof(f2,axiom,(
% 2.83/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f18,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/1.00    inference(ennf_transformation,[],[f2])).
% 2.83/1.00  
% 2.83/1.00  fof(f42,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/1.00    inference(nnf_transformation,[],[f18])).
% 2.83/1.00  
% 2.83/1.00  fof(f54,plain,(
% 2.83/1.00    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f42])).
% 2.83/1.00  
% 2.83/1.00  fof(f10,axiom,(
% 2.83/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f33,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.83/1.00    inference(ennf_transformation,[],[f10])).
% 2.83/1.00  
% 2.83/1.00  fof(f34,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.83/1.00    inference(flattening,[],[f33])).
% 2.83/1.00  
% 2.83/1.00  fof(f47,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.83/1.00    inference(nnf_transformation,[],[f34])).
% 2.83/1.00  
% 2.83/1.00  fof(f70,plain,(
% 2.83/1.00    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f47])).
% 2.83/1.00  
% 2.83/1.00  fof(f77,plain,(
% 2.83/1.00    ~v2_struct_0(sK1)),
% 2.83/1.00    inference(cnf_transformation,[],[f52])).
% 2.83/1.00  
% 2.83/1.00  fof(f78,plain,(
% 2.83/1.00    v2_pre_topc(sK1)),
% 2.83/1.00    inference(cnf_transformation,[],[f52])).
% 2.83/1.00  
% 2.83/1.00  fof(f12,axiom,(
% 2.83/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f37,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.83/1.00    inference(ennf_transformation,[],[f12])).
% 2.83/1.00  
% 2.83/1.00  fof(f38,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.83/1.00    inference(flattening,[],[f37])).
% 2.83/1.00  
% 2.83/1.00  fof(f75,plain,(
% 2.83/1.00    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f38])).
% 2.83/1.00  
% 2.83/1.00  fof(f86,plain,(
% 2.83/1.00    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(equality_resolution,[],[f75])).
% 2.83/1.00  
% 2.83/1.00  fof(f80,plain,(
% 2.83/1.00    ~v2_struct_0(sK2)),
% 2.83/1.00    inference(cnf_transformation,[],[f52])).
% 2.83/1.00  
% 2.83/1.00  fof(f5,axiom,(
% 2.83/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f23,plain,(
% 2.83/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.83/1.00    inference(ennf_transformation,[],[f5])).
% 2.83/1.00  
% 2.83/1.00  fof(f24,plain,(
% 2.83/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.83/1.00    inference(flattening,[],[f23])).
% 2.83/1.00  
% 2.83/1.00  fof(f58,plain,(
% 2.83/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f24])).
% 2.83/1.00  
% 2.83/1.00  fof(f6,axiom,(
% 2.83/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f25,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.83/1.00    inference(ennf_transformation,[],[f6])).
% 2.83/1.00  
% 2.83/1.00  fof(f26,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.83/1.00    inference(flattening,[],[f25])).
% 2.83/1.00  
% 2.83/1.00  fof(f59,plain,(
% 2.83/1.00    ( ! [X0,X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f26])).
% 2.83/1.00  
% 2.83/1.00  fof(f3,axiom,(
% 2.83/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f19,plain,(
% 2.83/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.83/1.00    inference(ennf_transformation,[],[f3])).
% 2.83/1.00  
% 2.83/1.00  fof(f20,plain,(
% 2.83/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.83/1.00    inference(flattening,[],[f19])).
% 2.83/1.00  
% 2.83/1.00  fof(f56,plain,(
% 2.83/1.00    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f20])).
% 2.83/1.00  
% 2.83/1.00  fof(f4,axiom,(
% 2.83/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f21,plain,(
% 2.83/1.00    ! [X0] : (k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.83/1.00    inference(ennf_transformation,[],[f4])).
% 2.83/1.00  
% 2.83/1.00  fof(f22,plain,(
% 2.83/1.00    ! [X0] : (k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.83/1.00    inference(flattening,[],[f21])).
% 2.83/1.00  
% 2.83/1.00  fof(f57,plain,(
% 2.83/1.00    ( ! [X0] : (k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f22])).
% 2.83/1.00  
% 2.83/1.00  fof(f11,axiom,(
% 2.83/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f35,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.83/1.00    inference(ennf_transformation,[],[f11])).
% 2.83/1.00  
% 2.83/1.00  fof(f36,plain,(
% 2.83/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.83/1.00    inference(flattening,[],[f35])).
% 2.83/1.00  
% 2.83/1.00  fof(f73,plain,(
% 2.83/1.00    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f36])).
% 2.83/1.00  
% 2.83/1.00  fof(f1,axiom,(
% 2.83/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f16,plain,(
% 2.83/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.83/1.00    inference(ennf_transformation,[],[f1])).
% 2.83/1.00  
% 2.83/1.00  fof(f17,plain,(
% 2.83/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.83/1.00    inference(flattening,[],[f16])).
% 2.83/1.00  
% 2.83/1.00  fof(f53,plain,(
% 2.83/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f17])).
% 2.83/1.00  
% 2.83/1.00  fof(f8,axiom,(
% 2.83/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f29,plain,(
% 2.83/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.83/1.00    inference(ennf_transformation,[],[f8])).
% 2.83/1.00  
% 2.83/1.00  fof(f30,plain,(
% 2.83/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.83/1.00    inference(flattening,[],[f29])).
% 2.83/1.00  
% 2.83/1.00  fof(f64,plain,(
% 2.83/1.00    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f30])).
% 2.83/1.00  
% 2.83/1.00  fof(f66,plain,(
% 2.83/1.00    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f30])).
% 2.83/1.00  
% 2.83/1.00  fof(f72,plain,(
% 2.83/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f36])).
% 2.83/1.00  
% 2.83/1.00  fof(f9,axiom,(
% 2.83/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.83/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.83/1.00  
% 2.83/1.00  fof(f31,plain,(
% 2.83/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.83/1.00    inference(ennf_transformation,[],[f9])).
% 2.83/1.00  
% 2.83/1.00  fof(f32,plain,(
% 2.83/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.83/1.00    inference(flattening,[],[f31])).
% 2.83/1.00  
% 2.83/1.00  fof(f67,plain,(
% 2.83/1.00    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f32])).
% 2.83/1.00  
% 2.83/1.00  fof(f69,plain,(
% 2.83/1.00    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f32])).
% 2.83/1.00  
% 2.83/1.00  fof(f74,plain,(
% 2.83/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f38])).
% 2.83/1.00  
% 2.83/1.00  fof(f62,plain,(
% 2.83/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f46])).
% 2.83/1.00  
% 2.83/1.00  fof(f84,plain,(
% 2.83/1.00    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)),
% 2.83/1.00    inference(cnf_transformation,[],[f52])).
% 2.83/1.00  
% 2.83/1.00  fof(f63,plain,(
% 2.83/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK0(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f46])).
% 2.83/1.00  
% 2.83/1.00  fof(f71,plain,(
% 2.83/1.00    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f47])).
% 2.83/1.00  
% 2.83/1.00  fof(f55,plain,(
% 2.83/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/1.00    inference(cnf_transformation,[],[f42])).
% 2.83/1.00  
% 2.83/1.00  cnf(c_10,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | ~ v1_tsep_1(X0,X1)
% 2.83/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.83/1.00      | ~ l1_pre_topc(X1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_23,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ l1_pre_topc(X1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_210,plain,
% 2.83/1.00      ( ~ v1_tsep_1(X0,X1)
% 2.83/1.00      | ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.83/1.00      | ~ l1_pre_topc(X1) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_10,c_23]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_211,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | ~ v1_tsep_1(X0,X1)
% 2.83/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.83/1.00      | ~ l1_pre_topc(X1) ),
% 2.83/1.00      inference(renaming,[status(thm)],[c_210]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_26,negated_conjecture,
% 2.83/1.00      ( v1_tsep_1(sK2,sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_261,plain,
% 2.83/1.00      ( v1_tsep_1(sK2,sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(prop_impl,[status(thm)],[c_26]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_671,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
% 2.83/1.00      | sK2 != X0
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_211,c_261]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_672,plain,
% 2.83/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.83/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_671]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_29,negated_conjecture,
% 2.83/1.00      ( l1_pre_topc(sK1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_27,negated_conjecture,
% 2.83/1.00      ( m1_pre_topc(sK2,sK1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_674,plain,
% 2.83/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_672,c_29,c_27]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1321,plain,
% 2.83/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_674]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2024,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
% 2.83/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_25,negated_conjecture,
% 2.83/1.00      ( m1_pre_topc(sK2,sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_181,negated_conjecture,
% 2.83/1.00      ( m1_pre_topc(sK2,sK1) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_25,c_27]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_761,plain,
% 2.83/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | sK2 != X0
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_181]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_762,plain,
% 2.83/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ l1_pre_topc(sK1) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_761]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_764,plain,
% 2.83/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_762,c_29]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1316,plain,
% 2.83/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_764]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2028,plain,
% 2.83/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1316]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 2.83/1.00      | ~ v3_pre_topc(X0,X1)
% 2.83/1.00      | ~ l1_pre_topc(X1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_18,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_542,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ v3_pre_topc(X0,X1)
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 2.83/1.00      inference(resolution,[status(thm)],[c_2,c_18]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_31,negated_conjecture,
% 2.83/1.00      ( ~ v2_struct_0(sK1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1019,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ v3_pre_topc(X0,X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_542,c_31]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1020,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ v3_pre_topc(X0,sK1)
% 2.83/1.00      | ~ v2_pre_topc(sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | k5_tmap_1(sK1,X0) = u1_pre_topc(sK1) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_1019]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_30,negated_conjecture,
% 2.83/1.00      ( v2_pre_topc(sK1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1024,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ v3_pre_topc(X0,sK1)
% 2.83/1.00      | k5_tmap_1(sK1,X0) = u1_pre_topc(sK1) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_1020,c_30,c_29]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1304,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ v3_pre_topc(X0_50,sK1)
% 2.83/1.00      | k5_tmap_1(sK1,X0_50) = u1_pre_topc(sK1) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_1024]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2045,plain,
% 2.83/1.00      ( k5_tmap_1(sK1,X0_50) = u1_pre_topc(sK1)
% 2.83/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/1.00      | v3_pre_topc(X0_50,sK1) != iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1304]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_3165,plain,
% 2.83/1.00      ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(sK1)
% 2.83/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_2028,c_2045]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_21,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | v2_struct_0(X0)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.83/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_193,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | v2_struct_0(X0)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_21,c_23]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_194,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | v2_struct_0(X0)
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.83/1.00      inference(renaming,[status(thm)],[c_193]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_753,plain,
% 2.83/1.00      ( v2_struct_0(X0)
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0))
% 2.83/1.00      | sK2 != X0
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_194,c_181]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_754,plain,
% 2.83/1.00      ( v2_struct_0(sK2)
% 2.83/1.00      | v2_struct_0(sK1)
% 2.83/1.00      | ~ v2_pre_topc(sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_753]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_28,negated_conjecture,
% 2.83/1.00      ( ~ v2_struct_0(sK2) ),
% 2.83/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_756,plain,
% 2.83/1.00      ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_754,c_31,c_30,c_29,c_28]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1317,plain,
% 2.83/1.00      ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_756]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_3168,plain,
% 2.83/1.00      ( u1_pre_topc(k8_tmap_1(sK1,sK2)) = u1_pre_topc(sK1)
% 2.83/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
% 2.83/1.00      inference(demodulation,[status(thm)],[c_3165,c_1317]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_3216,plain,
% 2.83/1.00      ( u1_pre_topc(k8_tmap_1(sK1,sK2)) = u1_pre_topc(sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_2024,c_3168]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_5,plain,
% 2.83/1.00      ( ~ m2_connsp_2(X0,X1,X2)
% 2.83/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_6,plain,
% 2.83/1.00      ( m2_connsp_2(k2_struct_0(X0),X0,X1)
% 2.83/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.83/1.00      | v2_struct_0(X0)
% 2.83/1.00      | ~ v2_pre_topc(X0)
% 2.83/1.00      | ~ l1_pre_topc(X0) ),
% 2.83/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_427,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.83/1.00      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | v2_struct_0(X3)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ v2_pre_topc(X3)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X3)
% 2.83/1.00      | X3 != X1
% 2.83/1.00      | X2 != X0
% 2.83/1.00      | k2_struct_0(X3) != X4 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_6]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_428,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_427]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1061,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_428,c_31]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1062,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ v2_pre_topc(sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_1061]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1066,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_1062,c_30,c_29]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1302,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_1066]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2047,plain,
% 2.83/1.00      ( m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1302]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_34,plain,
% 2.83/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_763,plain,
% 2.83/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.83/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2332,plain,
% 2.83/1.00      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.83/1.00      inference(instantiation,[status(thm)],[c_1302]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2333,plain,
% 2.83/1.00      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.83/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_2332]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2882,plain,
% 2.83/1.00      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_2047,c_34,c_763,c_2333]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_3164,plain,
% 2.83/1.00      ( k5_tmap_1(sK1,k2_struct_0(sK1)) = u1_pre_topc(sK1)
% 2.83/1.00      | v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_2882,c_2045]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_33,plain,
% 2.83/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2547,plain,
% 2.83/1.00      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ v3_pre_topc(k2_struct_0(sK1),sK1)
% 2.83/1.00      | k5_tmap_1(sK1,k2_struct_0(sK1)) = u1_pre_topc(sK1) ),
% 2.83/1.00      inference(instantiation,[status(thm)],[c_1304]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2548,plain,
% 2.83/1.00      ( k5_tmap_1(sK1,k2_struct_0(sK1)) = u1_pre_topc(sK1)
% 2.83/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/1.00      | v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_2547]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_3,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | v3_pre_topc(k1_tops_1(X1,X0),X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1328,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.83/1.00      | v3_pre_topc(k1_tops_1(X0_52,X0_50),X0_52)
% 2.83/1.00      | ~ v2_pre_topc(X0_52)
% 2.83/1.00      | ~ l1_pre_topc(X0_52) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2018,plain,
% 2.83/1.00      ( m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.83/1.00      | v3_pre_topc(k1_tops_1(X0_52,X0_50),X0_52) = iProver_top
% 2.83/1.00      | v2_pre_topc(X0_52) != iProver_top
% 2.83/1.00      | l1_pre_topc(X0_52) != iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1328]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2890,plain,
% 2.83/1.00      ( v3_pre_topc(k1_tops_1(sK1,k2_struct_0(sK1)),sK1) = iProver_top
% 2.83/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.83/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_2882,c_2018]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1325,negated_conjecture,
% 2.83/1.00      ( v2_pre_topc(sK1) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2021,plain,
% 2.83/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1325]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_4,plain,
% 2.83/1.00      ( ~ v2_pre_topc(X0)
% 2.83/1.00      | ~ l1_pre_topc(X0)
% 2.83/1.00      | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 2.83/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1327,plain,
% 2.83/1.00      ( ~ v2_pre_topc(X0_52)
% 2.83/1.00      | ~ l1_pre_topc(X0_52)
% 2.83/1.00      | k1_tops_1(X0_52,k2_struct_0(X0_52)) = k2_struct_0(X0_52) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2019,plain,
% 2.83/1.00      ( k1_tops_1(X0_52,k2_struct_0(X0_52)) = k2_struct_0(X0_52)
% 2.83/1.00      | v2_pre_topc(X0_52) != iProver_top
% 2.83/1.00      | l1_pre_topc(X0_52) != iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1327]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2377,plain,
% 2.83/1.00      ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1)
% 2.83/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_2021,c_2019]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1390,plain,
% 2.83/1.00      ( ~ v2_pre_topc(sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 2.83/1.00      inference(instantiation,[status(thm)],[c_1327]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2430,plain,
% 2.83/1.00      ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_2377,c_30,c_29,c_1390]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2894,plain,
% 2.83/1.00      ( v3_pre_topc(k2_struct_0(sK1),sK1) = iProver_top
% 2.83/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.83/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.83/1.00      inference(light_normalisation,[status(thm)],[c_2890,c_2430]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_4050,plain,
% 2.83/1.00      ( k5_tmap_1(sK1,k2_struct_0(sK1)) = u1_pre_topc(sK1) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_3164,c_33,c_34,c_763,c_2333,c_2548,c_2894]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_19,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 2.83/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1097,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1098,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ v2_pre_topc(sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_1097]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1102,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_1098,c_30,c_29]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1300,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0_50)) = k5_tmap_1(sK1,X0_50) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_1102]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2049,plain,
% 2.83/1.00      ( u1_pre_topc(k6_tmap_1(sK1,X0_50)) = k5_tmap_1(sK1,X0_50)
% 2.83/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1300]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2910,plain,
% 2.83/1.00      ( u1_pre_topc(k6_tmap_1(sK1,k2_struct_0(sK1))) = k5_tmap_1(sK1,k2_struct_0(sK1)) ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_2882,c_2049]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_4053,plain,
% 2.83/1.00      ( u1_pre_topc(k6_tmap_1(sK1,k2_struct_0(sK1))) = u1_pre_topc(sK1) ),
% 2.83/1.00      inference(demodulation,[status(thm)],[c_4050,c_2910]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_0,plain,
% 2.83/1.00      ( ~ l1_pre_topc(X0)
% 2.83/1.00      | ~ v1_pre_topc(X0)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.83/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_13,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | v1_pre_topc(k6_tmap_1(X1,X0)) ),
% 2.83/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1115,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | v1_pre_topc(k6_tmap_1(X1,X0))
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1116,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ v2_pre_topc(sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | v1_pre_topc(k6_tmap_1(sK1,X0)) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_1115]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1120,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | v1_pre_topc(k6_tmap_1(sK1,X0)) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_1116,c_30,c_29]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1269,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | k6_tmap_1(sK1,X0) != X1
% 2.83/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_1120]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1270,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ l1_pre_topc(k6_tmap_1(sK1,X0))
% 2.83/1.00      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_1269]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_11,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 2.83/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1151,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | l1_pre_topc(k6_tmap_1(X1,X0))
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_31]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1152,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ v2_pre_topc(sK1)
% 2.83/1.00      | l1_pre_topc(k6_tmap_1(sK1,X0))
% 2.83/1.00      | ~ l1_pre_topc(sK1) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_1151]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1274,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_1270,c_30,c_29,c_1152]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1296,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0_50)),u1_pre_topc(k6_tmap_1(sK1,X0_50))) = k6_tmap_1(sK1,X0_50) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_1274]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2054,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0_50)),u1_pre_topc(k6_tmap_1(sK1,X0_50))) = k6_tmap_1(sK1,X0_50)
% 2.83/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1296]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_3660,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,k2_struct_0(sK1))),u1_pre_topc(k6_tmap_1(sK1,k2_struct_0(sK1)))) = k6_tmap_1(sK1,k2_struct_0(sK1)) ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_2882,c_2054]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_20,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1079,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1080,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | ~ v2_pre_topc(sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_1079]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1084,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_1080,c_30,c_29]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1301,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | u1_struct_0(k6_tmap_1(sK1,X0_50)) = u1_struct_0(sK1) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_1084]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2048,plain,
% 2.83/1.00      ( u1_struct_0(k6_tmap_1(sK1,X0_50)) = u1_struct_0(sK1)
% 2.83/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1301]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2887,plain,
% 2.83/1.00      ( u1_struct_0(k6_tmap_1(sK1,k2_struct_0(sK1))) = u1_struct_0(sK1) ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_2882,c_2048]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_4289,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k6_tmap_1(sK1,k2_struct_0(sK1)))) = k6_tmap_1(sK1,k2_struct_0(sK1)) ),
% 2.83/1.00      inference(light_normalisation,[status(thm)],[c_3660,c_2887]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_5082,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,k2_struct_0(sK1)) ),
% 2.83/1.00      inference(demodulation,[status(thm)],[c_4053,c_4289]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_5147,plain,
% 2.83/1.00      ( u1_pre_topc(k8_tmap_1(sK1,sK2)) = u1_pre_topc(sK1)
% 2.83/1.00      | k6_tmap_1(sK1,k2_struct_0(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_3216,c_5082]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_5192,plain,
% 2.83/1.00      ( u1_pre_topc(k8_tmap_1(sK1,sK2)) = u1_pre_topc(sK1) ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_5147,c_4053]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_16,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | v1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.83/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_780,plain,
% 2.83/1.00      ( v2_struct_0(X0)
% 2.83/1.00      | ~ v2_pre_topc(X0)
% 2.83/1.00      | ~ l1_pre_topc(X0)
% 2.83/1.00      | v1_pre_topc(k8_tmap_1(X0,X1))
% 2.83/1.00      | sK2 != X1
% 2.83/1.00      | sK1 != X0 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_181]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_781,plain,
% 2.83/1.00      ( v2_struct_0(sK1)
% 2.83/1.00      | ~ v2_pre_topc(sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | v1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_780]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_783,plain,
% 2.83/1.00      ( v1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_781,c_31,c_30,c_29]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1237,plain,
% 2.83/1.00      ( ~ l1_pre_topc(X0)
% 2.83/1.00      | k8_tmap_1(sK1,sK2) != X0
% 2.83/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_783]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1238,plain,
% 2.83/1.00      ( ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.83/1.00      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_1237]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_14,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.83/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_802,plain,
% 2.83/1.00      ( v2_struct_0(X0)
% 2.83/1.00      | ~ v2_pre_topc(X0)
% 2.83/1.00      | ~ l1_pre_topc(X0)
% 2.83/1.00      | l1_pre_topc(k8_tmap_1(X0,X1))
% 2.83/1.00      | sK2 != X1
% 2.83/1.00      | sK1 != X0 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_181]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_803,plain,
% 2.83/1.00      ( v2_struct_0(sK1)
% 2.83/1.00      | ~ v2_pre_topc(sK1)
% 2.83/1.00      | l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.83/1.00      | ~ l1_pre_topc(sK1) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_802]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_855,plain,
% 2.83/1.00      ( ~ l1_pre_topc(X0)
% 2.83/1.00      | k8_tmap_1(sK1,sK2) != X0
% 2.83/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_783]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_856,plain,
% 2.83/1.00      ( ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.83/1.00      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_855]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1240,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_1238,c_31,c_30,c_29,c_803,c_856]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1312,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_1240]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_22,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | v2_struct_0(X0)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_772,plain,
% 2.83/1.00      ( v2_struct_0(X0)
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.83/1.00      | sK2 != X0
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_181]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_773,plain,
% 2.83/1.00      ( v2_struct_0(sK2)
% 2.83/1.00      | v2_struct_0(sK1)
% 2.83/1.00      | ~ v2_pre_topc(sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_772]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_775,plain,
% 2.83/1.00      ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_773,c_31,c_30,c_29,c_28]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1315,plain,
% 2.83/1.00      ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_775]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2073,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(light_normalisation,[status(thm)],[c_1312,c_1315]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_5298,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(demodulation,[status(thm)],[c_5192,c_2073]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_8,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | v1_tsep_1(X0,X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.83/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_597,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.83/1.00      inference(resolution,[status(thm)],[c_8,c_211]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_725,plain,
% 2.83/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | sK0(X1,X0) = u1_struct_0(X0)
% 2.83/1.00      | sK2 != X0
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_597,c_181]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_726,plain,
% 2.83/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_725]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_728,plain,
% 2.83/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.83/1.00      | sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_726,c_29]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1319,plain,
% 2.83/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.83/1.00      | sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_728]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2026,plain,
% 2.83/1.00      ( sK0(sK1,sK2) = u1_struct_0(sK2)
% 2.83/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_3314,plain,
% 2.83/1.00      ( u1_pre_topc(k8_tmap_1(sK1,sK2)) = u1_pre_topc(sK1)
% 2.83/1.00      | sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_2026,c_3168]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_4294,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
% 2.83/1.00      | sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_3314,c_2073]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_24,negated_conjecture,
% 2.83/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.83/1.00      | ~ v1_tsep_1(sK2,sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_259,plain,
% 2.83/1.00      ( ~ v1_tsep_1(sK2,sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(prop_impl,[status(thm)],[c_27,c_24]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_646,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | sK0(X1,X0) = u1_struct_0(X0)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
% 2.83/1.00      | sK2 != X0
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_259]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_647,plain,
% 2.83/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | sK0(sK1,sK2) = u1_struct_0(sK2)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_646]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_649,plain,
% 2.83/1.00      ( sK0(sK1,sK2) = u1_struct_0(sK2)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_647,c_29,c_27]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1323,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
% 2.83/1.00      | sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_649]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_4426,plain,
% 2.83/1.00      ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_4294,c_1323]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_7,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | v1_tsep_1(X0,X1)
% 2.83/1.00      | ~ v3_pre_topc(sK0(X1,X0),X1)
% 2.83/1.00      | ~ l1_pre_topc(X1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_657,plain,
% 2.83/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.83/1.00      | ~ v3_pre_topc(sK0(X1,X0),X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
% 2.83/1.00      | sK2 != X0
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_259]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_658,plain,
% 2.83/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.83/1.00      | ~ v3_pre_topc(sK0(sK1,sK2),sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_657]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_660,plain,
% 2.83/1.00      ( ~ v3_pre_topc(sK0(sK1,sK2),sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_658,c_29,c_27]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1322,plain,
% 2.83/1.00      ( ~ v3_pre_topc(sK0(sK1,sK2),sK1)
% 2.83/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_660]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2023,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
% 2.83/1.00      | v3_pre_topc(sK0(sK1,sK2),sK1) != iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1322]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_4434,plain,
% 2.83/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
% 2.83/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
% 2.83/1.00      inference(demodulation,[status(thm)],[c_4426,c_2023]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_17,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.83/1.00      | v3_pre_topc(X0,X1)
% 2.83/1.00      | ~ l1_pre_topc(X1) ),
% 2.83/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_519,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | v3_pre_topc(X0,X1)
% 2.83/1.00      | v2_struct_0(X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 2.83/1.00      inference(resolution,[status(thm)],[c_17,c_1]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1040,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/1.00      | v3_pre_topc(X0,X1)
% 2.83/1.00      | ~ v2_pre_topc(X1)
% 2.83/1.00      | ~ l1_pre_topc(X1)
% 2.83/1.00      | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
% 2.83/1.00      | sK1 != X1 ),
% 2.83/1.00      inference(resolution_lifted,[status(thm)],[c_519,c_31]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1041,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | v3_pre_topc(X0,sK1)
% 2.83/1.00      | ~ v2_pre_topc(sK1)
% 2.83/1.00      | ~ l1_pre_topc(sK1)
% 2.83/1.00      | k5_tmap_1(sK1,X0) != u1_pre_topc(sK1) ),
% 2.83/1.00      inference(unflattening,[status(thm)],[c_1040]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1045,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | v3_pre_topc(X0,sK1)
% 2.83/1.00      | k5_tmap_1(sK1,X0) != u1_pre_topc(sK1) ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_1041,c_30,c_29]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_1303,plain,
% 2.83/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/1.00      | v3_pre_topc(X0_50,sK1)
% 2.83/1.00      | k5_tmap_1(sK1,X0_50) != u1_pre_topc(sK1) ),
% 2.83/1.00      inference(subtyping,[status(esa)],[c_1045]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_2046,plain,
% 2.83/1.00      ( k5_tmap_1(sK1,X0_50) != u1_pre_topc(sK1)
% 2.83/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/1.00      | v3_pre_topc(X0_50,sK1) = iProver_top ),
% 2.83/1.00      inference(predicate_to_equality,[status(thm)],[c_1303]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_3211,plain,
% 2.83/1.00      ( u1_pre_topc(k8_tmap_1(sK1,sK2)) != u1_pre_topc(sK1)
% 2.83/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
% 2.83/1.00      inference(superposition,[status(thm)],[c_1317,c_2046]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(c_3278,plain,
% 2.83/1.00      ( u1_pre_topc(k8_tmap_1(sK1,sK2)) != u1_pre_topc(sK1)
% 2.83/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
% 2.83/1.00      inference(global_propositional_subsumption,
% 2.83/1.00                [status(thm)],
% 2.83/1.00                [c_3211,c_34,c_763]) ).
% 2.83/1.00  
% 2.83/1.00  cnf(contradiction,plain,
% 2.83/1.00      ( $false ),
% 2.83/1.00      inference(minisat,[status(thm)],[c_5298,c_5192,c_4434,c_3278]) ).
% 2.83/1.00  
% 2.83/1.00  
% 2.83/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.83/1.00  
% 2.83/1.00  ------                               Statistics
% 2.83/1.00  
% 2.83/1.00  ------ General
% 2.83/1.00  
% 2.83/1.00  abstr_ref_over_cycles:                  0
% 2.83/1.00  abstr_ref_under_cycles:                 0
% 2.83/1.00  gc_basic_clause_elim:                   0
% 2.83/1.00  forced_gc_time:                         0
% 2.83/1.00  parsing_time:                           0.009
% 2.83/1.00  unif_index_cands_time:                  0.
% 2.83/1.00  unif_index_add_time:                    0.
% 2.83/1.00  orderings_time:                         0.
% 2.83/1.00  out_proof_time:                         0.015
% 2.83/1.00  total_time:                             0.149
% 2.83/1.00  num_of_symbols:                         65
% 2.83/1.00  num_of_terms:                           2871
% 2.83/1.00  
% 2.83/1.00  ------ Preprocessing
% 2.83/1.00  
% 2.83/1.00  num_of_splits:                          8
% 2.83/1.00  num_of_split_atoms:                     8
% 2.83/1.00  num_of_reused_defs:                     0
% 2.83/1.00  num_eq_ax_congr_red:                    13
% 2.83/1.00  num_of_sem_filtered_clauses:            1
% 2.83/1.00  num_of_subtypes:                        4
% 2.83/1.00  monotx_restored_types:                  0
% 2.83/1.00  sat_num_of_epr_types:                   0
% 2.83/1.00  sat_num_of_non_cyclic_types:            0
% 2.83/1.00  sat_guarded_non_collapsed_types:        0
% 2.83/1.00  num_pure_diseq_elim:                    0
% 2.83/1.00  simp_replaced_by:                       0
% 2.83/1.00  res_preprocessed:                       156
% 2.83/1.00  prep_upred:                             0
% 2.83/1.00  prep_unflattend:                        52
% 2.83/1.00  smt_new_axioms:                         0
% 2.83/1.00  pred_elim_cands:                        10
% 2.83/1.00  pred_elim:                              6
% 2.83/1.00  pred_elim_cl:                           -2
% 2.83/1.00  pred_elim_cycles:                       9
% 2.83/1.00  merged_defs:                            2
% 2.83/1.00  merged_defs_ncl:                        0
% 2.83/1.00  bin_hyper_res:                          2
% 2.83/1.00  prep_cycles:                            3
% 2.83/1.00  pred_elim_time:                         0.01
% 2.83/1.00  splitting_time:                         0.
% 2.83/1.00  sem_filter_time:                        0.
% 2.83/1.00  monotx_time:                            0.
% 2.83/1.00  subtype_inf_time:                       0.
% 2.83/1.00  
% 2.83/1.00  ------ Problem properties
% 2.83/1.00  
% 2.83/1.00  clauses:                                41
% 2.83/1.00  conjectures:                            2
% 2.83/1.00  epr:                                    9
% 2.83/1.00  horn:                                   37
% 2.83/1.00  ground:                                 23
% 2.83/1.00  unary:                                  8
% 2.83/1.00  binary:                                 14
% 2.83/1.00  lits:                                   97
% 2.83/1.00  lits_eq:                                20
% 2.83/1.00  fd_pure:                                0
% 2.83/1.00  fd_pseudo:                              0
% 2.83/1.00  fd_cond:                                0
% 2.83/1.00  fd_pseudo_cond:                         0
% 2.83/1.00  ac_symbols:                             0
% 2.83/1.00  
% 2.83/1.00  ------ Propositional Solver
% 2.83/1.00  
% 2.83/1.00  prop_solver_calls:                      26
% 2.83/1.00  prop_fast_solver_calls:                 1369
% 2.83/1.00  smt_solver_calls:                       0
% 2.83/1.00  smt_fast_solver_calls:                  0
% 2.83/1.00  prop_num_of_clauses:                    1572
% 2.83/1.00  prop_preprocess_simplified:             6261
% 2.83/1.00  prop_fo_subsumed:                       92
% 2.83/1.00  prop_solver_time:                       0.
% 2.83/1.00  smt_solver_time:                        0.
% 2.83/1.00  smt_fast_solver_time:                   0.
% 2.83/1.00  prop_fast_solver_time:                  0.
% 2.83/1.00  prop_unsat_core_time:                   0.
% 2.83/1.00  
% 2.83/1.00  ------ QBF
% 2.83/1.00  
% 2.83/1.00  qbf_q_res:                              0
% 2.83/1.00  qbf_num_tautologies:                    0
% 2.83/1.00  qbf_prep_cycles:                        0
% 2.83/1.00  
% 2.83/1.00  ------ BMC1
% 2.83/1.00  
% 2.83/1.00  bmc1_current_bound:                     -1
% 2.83/1.00  bmc1_last_solved_bound:                 -1
% 2.83/1.00  bmc1_unsat_core_size:                   -1
% 2.83/1.00  bmc1_unsat_core_parents_size:           -1
% 2.83/1.00  bmc1_merge_next_fun:                    0
% 2.83/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.83/1.00  
% 2.83/1.00  ------ Instantiation
% 2.83/1.00  
% 2.83/1.00  inst_num_of_clauses:                    552
% 2.83/1.00  inst_num_in_passive:                    154
% 2.83/1.00  inst_num_in_active:                     361
% 2.83/1.00  inst_num_in_unprocessed:                37
% 2.83/1.00  inst_num_of_loops:                      430
% 2.83/1.00  inst_num_of_learning_restarts:          0
% 2.83/1.00  inst_num_moves_active_passive:          64
% 2.83/1.00  inst_lit_activity:                      0
% 2.83/1.00  inst_lit_activity_moves:                0
% 2.83/1.00  inst_num_tautologies:                   0
% 2.83/1.00  inst_num_prop_implied:                  0
% 2.83/1.00  inst_num_existing_simplified:           0
% 2.83/1.00  inst_num_eq_res_simplified:             0
% 2.83/1.00  inst_num_child_elim:                    0
% 2.83/1.00  inst_num_of_dismatching_blockings:      85
% 2.83/1.00  inst_num_of_non_proper_insts:           583
% 2.83/1.00  inst_num_of_duplicates:                 0
% 2.83/1.00  inst_inst_num_from_inst_to_res:         0
% 2.83/1.00  inst_dismatching_checking_time:         0.
% 2.83/1.00  
% 2.83/1.00  ------ Resolution
% 2.83/1.00  
% 2.83/1.00  res_num_of_clauses:                     0
% 2.83/1.00  res_num_in_passive:                     0
% 2.83/1.00  res_num_in_active:                      0
% 2.83/1.00  res_num_of_loops:                       159
% 2.83/1.00  res_forward_subset_subsumed:            103
% 2.83/1.00  res_backward_subset_subsumed:           0
% 2.83/1.00  res_forward_subsumed:                   0
% 2.83/1.00  res_backward_subsumed:                  0
% 2.83/1.00  res_forward_subsumption_resolution:     0
% 2.83/1.00  res_backward_subsumption_resolution:    0
% 2.83/1.00  res_clause_to_clause_subsumption:       102
% 2.83/1.00  res_orphan_elimination:                 0
% 2.83/1.00  res_tautology_del:                      113
% 2.83/1.00  res_num_eq_res_simplified:              0
% 2.83/1.00  res_num_sel_changes:                    0
% 2.83/1.00  res_moves_from_active_to_pass:          0
% 2.83/1.00  
% 2.83/1.00  ------ Superposition
% 2.83/1.00  
% 2.83/1.00  sup_time_total:                         0.
% 2.83/1.00  sup_time_generating:                    0.
% 2.83/1.00  sup_time_sim_full:                      0.
% 2.83/1.00  sup_time_sim_immed:                     0.
% 2.83/1.00  
% 2.83/1.00  sup_num_of_clauses:                     61
% 2.83/1.00  sup_num_in_active:                      59
% 2.83/1.00  sup_num_in_passive:                     2
% 2.83/1.00  sup_num_of_loops:                       85
% 2.83/1.00  sup_fw_superposition:                   21
% 2.83/1.00  sup_bw_superposition:                   40
% 2.83/1.00  sup_immediate_simplified:               17
% 2.83/1.00  sup_given_eliminated:                   0
% 2.83/1.00  comparisons_done:                       0
% 2.83/1.00  comparisons_avoided:                    9
% 2.83/1.00  
% 2.83/1.00  ------ Simplifications
% 2.83/1.00  
% 2.83/1.00  
% 2.83/1.00  sim_fw_subset_subsumed:                 9
% 2.83/1.00  sim_bw_subset_subsumed:                 8
% 2.83/1.00  sim_fw_subsumed:                        0
% 2.83/1.00  sim_bw_subsumed:                        0
% 2.83/1.00  sim_fw_subsumption_res:                 0
% 2.83/1.00  sim_bw_subsumption_res:                 0
% 2.83/1.00  sim_tautology_del:                      2
% 2.83/1.00  sim_eq_tautology_del:                   5
% 2.83/1.00  sim_eq_res_simp:                        1
% 2.83/1.00  sim_fw_demodulated:                     1
% 2.83/1.00  sim_bw_demodulated:                     21
% 2.83/1.00  sim_light_normalised:                   12
% 2.83/1.00  sim_joinable_taut:                      0
% 2.83/1.00  sim_joinable_simp:                      0
% 2.83/1.00  sim_ac_normalised:                      0
% 2.83/1.00  sim_smt_subsumption:                    0
% 2.83/1.00  
%------------------------------------------------------------------------------
