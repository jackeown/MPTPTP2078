%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:03 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  237 (6071 expanded)
%              Number of clauses        :  165 (1448 expanded)
%              Number of leaves         :   15 (1354 expanded)
%              Depth                    :   25
%              Number of atoms          :  976 (46600 expanded)
%              Number of equality atoms :  272 (8399 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

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
     => ( ~ v3_pre_topc(sK4(X0,X1),X0)
        & u1_struct_0(X1) = sK4(X0,X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK4(X0,X1),X0)
                & u1_struct_0(X1) = sK4(X0,X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

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
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK6)
          | ~ m1_pre_topc(sK6,X0)
          | ~ v1_tsep_1(sK6,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK6)
          | ( m1_pre_topc(sK6,X0)
            & v1_tsep_1(sK6,X0) ) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
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
          ( ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,X1)
            | ~ m1_pre_topc(X1,sK5)
            | ~ v1_tsep_1(X1,sK5) )
          & ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,X1)
            | ( m1_pre_topc(X1,sK5)
              & v1_tsep_1(X1,sK5) ) )
          & m1_pre_topc(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6)
      | ~ m1_pre_topc(sK6,sK5)
      | ~ v1_tsep_1(sK6,sK5) )
    & ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6)
      | ( m1_pre_topc(sK6,sK5)
        & v1_tsep_1(sK6,sK5) ) )
    & m1_pre_topc(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f49,f51,f50])).

fof(f86,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6)
    | v1_tsep_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6)
    | m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

fof(f75,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f84,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f30])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f53,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK4(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ v1_tsep_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK4(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_226,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_26])).

cnf(c_227,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_226])).

cnf(c_30,negated_conjecture,
    ( v1_tsep_1(sK6,sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_295,plain,
    ( v1_tsep_1(sK6,sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_731,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_227,c_295])).

cnf(c_732,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | v3_pre_topc(u1_struct_0(sK6),sK5)
    | ~ l1_pre_topc(sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_734,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_732,c_33,c_31])).

cnf(c_1960,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_734])).

cnf(c_2751,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6)
    | v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1960])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK6,sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_201,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_31])).

cnf(c_968,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_201])).

cnf(c_969,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_968])).

cnf(c_971,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_969,c_33])).

cnf(c_1951,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_971])).

cnf(c_2759,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1951])).

cnf(c_14,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1966,plain,
    ( ~ v3_pre_topc(X0_54,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | r2_hidden(X0_54,u1_pre_topc(X0_53))
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2746,plain,
    ( v3_pre_topc(X0_54,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
    | r2_hidden(X0_54,u1_pre_topc(X0_53)) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1966])).

cnf(c_3746,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2759,c_2746])).

cnf(c_38,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5780,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3746,c_38])).

cnf(c_5781,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5780])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_1273,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,u1_pre_topc(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | k5_tmap_1(sK5,X0) = u1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_1272])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,u1_pre_topc(sK5))
    | k5_tmap_1(sK5,X0) = u1_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1273,c_34,c_33])).

cnf(c_1936,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0_54,u1_pre_topc(sK5))
    | k5_tmap_1(sK5,X0_54) = u1_pre_topc(sK5) ),
    inference(subtyping,[status(esa)],[c_1277])).

cnf(c_2772,plain,
    ( k5_tmap_1(sK5,X0_54) = u1_pre_topc(sK5)
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0_54,u1_pre_topc(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_3979,plain,
    ( k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(sK5)
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2759,c_2772])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_214,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_26])).

cnf(c_215,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_960,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0))
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_215,c_201])).

cnf(c_961,plain,
    ( v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(k8_tmap_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_960])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_963,plain,
    ( k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(k8_tmap_1(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_961,c_35,c_34,c_33,c_32])).

cnf(c_1952,plain,
    ( k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(k8_tmap_1(sK5,sK6)) ),
    inference(subtyping,[status(esa)],[c_963])).

cnf(c_3984,plain,
    ( u1_pre_topc(k8_tmap_1(sK5,sK6)) = u1_pre_topc(sK5)
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3979,c_1952])).

cnf(c_5787,plain,
    ( u1_pre_topc(k8_tmap_1(sK5,sK6)) = u1_pre_topc(sK5)
    | v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5781,c_3984])).

cnf(c_6115,plain,
    ( u1_pre_topc(k8_tmap_1(sK5,sK6)) = u1_pre_topc(sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_2751,c_5787])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_27,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_846,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_847,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X0)) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_846])).

cnf(c_1214,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X0)) = u1_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_847,c_35])).

cnf(c_1215,plain,
    ( ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(k8_tmap_1(sK5,sK5)) = u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1214])).

cnf(c_45,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_51,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(k8_tmap_1(sK5,sK5)) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1217,plain,
    ( u1_struct_0(k8_tmap_1(sK5,sK5)) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1215,c_35,c_34,c_33,c_45,c_51])).

cnf(c_1940,plain,
    ( u1_struct_0(k8_tmap_1(sK5,sK5)) = u1_struct_0(sK5) ),
    inference(subtyping,[status(esa)],[c_1217])).

cnf(c_834,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_27])).

cnf(c_835,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_1956,plain,
    ( m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_835])).

cnf(c_2755,plain,
    ( m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X0_53))) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1956])).

cnf(c_7165,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK5,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1940,c_2755])).

cnf(c_44,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_46,plain,
    ( m1_pre_topc(sK5,sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_47,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_49,plain,
    ( m1_pre_topc(sK5,sK5) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_7328,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7165,c_38,c_46,c_49])).

cnf(c_7333,plain,
    ( k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(sK5)
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7328,c_2772])).

cnf(c_816,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(resolution_lifted,[status(thm)],[c_215,c_27])).

cnf(c_817,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X0,X0)) ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_1222,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X0,X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_817,c_35])).

cnf(c_1223,plain,
    ( ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(k8_tmap_1(sK5,sK5)) ),
    inference(unflattening,[status(thm)],[c_1222])).

cnf(c_48,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_54,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(k8_tmap_1(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1225,plain,
    ( k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(k8_tmap_1(sK5,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1223,c_35,c_34,c_33,c_45,c_48,c_54])).

cnf(c_1939,plain,
    ( k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(k8_tmap_1(sK5,sK5)) ),
    inference(subtyping,[status(esa)],[c_1225])).

cnf(c_7344,plain,
    ( u1_pre_topc(k8_tmap_1(sK5,sK5)) = u1_pre_topc(sK5)
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7333,c_1939])).

cnf(c_37,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_12,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_89,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_91,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_7167,plain,
    ( k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(sK5)
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2755,c_2772])).

cnf(c_7194,plain,
    ( u1_pre_topc(k8_tmap_1(sK5,sK5)) = u1_pre_topc(sK5)
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7167,c_1939])).

cnf(c_7350,plain,
    ( u1_pre_topc(k8_tmap_1(sK5,sK5)) = u1_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7344,c_37,c_38,c_91,c_7194])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_864,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k8_tmap_1(X0,X2))
    | X1 != X0
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_865,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(k8_tmap_1(X0,X0)) ),
    inference(unflattening,[status(thm)],[c_864])).

cnf(c_1203,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(k8_tmap_1(X0,X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_865,c_35])).

cnf(c_1204,plain,
    ( ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | v1_pre_topc(k8_tmap_1(sK5,sK5)) ),
    inference(unflattening,[status(thm)],[c_1203])).

cnf(c_63,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | v1_pre_topc(k8_tmap_1(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1206,plain,
    ( v1_pre_topc(k8_tmap_1(sK5,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1204,c_35,c_34,c_33,c_45,c_63])).

cnf(c_1362,plain,
    ( ~ l1_pre_topc(X0)
    | k8_tmap_1(sK5,sK5) != X0
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1206])).

cnf(c_1363,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK5,sK5))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK5)),u1_pre_topc(k8_tmap_1(sK5,sK5))) = k8_tmap_1(sK5,sK5) ),
    inference(unflattening,[status(thm)],[c_1362])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_69,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | l1_pre_topc(k8_tmap_1(sK5,sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_483,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k8_tmap_1(X1,X0) != X2
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_484,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0))) = k8_tmap_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_486,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(k8_tmap_1(sK5,sK5))
    | ~ l1_pre_topc(sK5)
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK5)),u1_pre_topc(k8_tmap_1(sK5,sK5))) = k8_tmap_1(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_1365,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK5)),u1_pre_topc(k8_tmap_1(sK5,sK5))) = k8_tmap_1(sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1363,c_35,c_34,c_33,c_45,c_69,c_486])).

cnf(c_1934,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK5)),u1_pre_topc(k8_tmap_1(sK5,sK5))) = k8_tmap_1(sK5,sK5) ),
    inference(subtyping,[status(esa)],[c_1365])).

cnf(c_2820,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(k8_tmap_1(sK5,sK5))) = k8_tmap_1(sK5,sK5) ),
    inference(light_normalisation,[status(thm)],[c_1934,c_1940])).

cnf(c_7360,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK5) ),
    inference(demodulation,[status(thm)],[c_7350,c_2820])).

cnf(c_8810,plain,
    ( u1_pre_topc(k8_tmap_1(sK5,sK6)) = u1_pre_topc(sK5)
    | k8_tmap_1(sK5,sK5) = k8_tmap_1(sK5,sK6) ),
    inference(light_normalisation,[status(thm)],[c_6115,c_7360])).

cnf(c_987,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(k8_tmap_1(X0,X1))
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_201])).

cnf(c_988,plain,
    ( v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | v1_pre_topc(k8_tmap_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_987])).

cnf(c_990,plain,
    ( v1_pre_topc(k8_tmap_1(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_988,c_35,c_34,c_33])).

cnf(c_1370,plain,
    ( ~ l1_pre_topc(X0)
    | k8_tmap_1(sK5,sK6) != X0
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_990])).

cnf(c_1371,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK5,sK6))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK6)),u1_pre_topc(k8_tmap_1(sK5,sK6))) = k8_tmap_1(sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_1370])).

cnf(c_1009,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_201])).

cnf(c_1010,plain,
    ( v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | l1_pre_topc(k8_tmap_1(sK5,sK6))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_1009])).

cnf(c_1103,plain,
    ( ~ l1_pre_topc(X0)
    | k8_tmap_1(sK5,sK6) != X0
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_990])).

cnf(c_1104,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK5,sK6))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK6)),u1_pre_topc(k8_tmap_1(sK5,sK6))) = k8_tmap_1(sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_1103])).

cnf(c_1373,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK6)),u1_pre_topc(k8_tmap_1(sK5,sK6))) = k8_tmap_1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1371,c_35,c_34,c_33,c_1010,c_1104])).

cnf(c_1947,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK6)),u1_pre_topc(k8_tmap_1(sK5,sK6))) = k8_tmap_1(sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_1373])).

cnf(c_979,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_201])).

cnf(c_980,plain,
    ( v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | u1_struct_0(k8_tmap_1(sK5,sK6)) = u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_979])).

cnf(c_982,plain,
    ( u1_struct_0(k8_tmap_1(sK5,sK6)) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_980,c_35,c_34,c_33,c_32])).

cnf(c_1950,plain,
    ( u1_struct_0(k8_tmap_1(sK5,sK6)) = u1_struct_0(sK5) ),
    inference(subtyping,[status(esa)],[c_982])).

cnf(c_2817,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(k8_tmap_1(sK5,sK6))) = k8_tmap_1(sK5,sK6) ),
    inference(light_normalisation,[status(thm)],[c_1947,c_1950])).

cnf(c_8819,plain,
    ( k8_tmap_1(sK5,sK5) = k8_tmap_1(sK5,sK6)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_8810,c_2817])).

cnf(c_8882,plain,
    ( k8_tmap_1(sK5,sK5) = k8_tmap_1(sK5,sK6) ),
    inference(light_normalisation,[status(thm)],[c_8819,c_7360])).

cnf(c_8904,plain,
    ( k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(k8_tmap_1(sK5,sK5)) ),
    inference(demodulation,[status(thm)],[c_8882,c_1952])).

cnf(c_8907,plain,
    ( k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(sK5) ),
    inference(light_normalisation,[status(thm)],[c_8904,c_7350])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK4(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_657,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | sK4(X1,X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_16,c_227])).

cnf(c_932,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | sK4(X1,X0) = u1_struct_0(X0)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_657,c_201])).

cnf(c_933,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5)
    | ~ l1_pre_topc(sK5)
    | sK4(sK5,sK6) = u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_932])).

cnf(c_935,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5)
    | sK4(sK5,sK6) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_933,c_33])).

cnf(c_1954,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5)
    | sK4(sK5,sK6) = u1_struct_0(sK6) ),
    inference(subtyping,[status(esa)],[c_935])).

cnf(c_2757,plain,
    ( sK4(sK5,sK6) = u1_struct_0(sK6)
    | v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1954])).

cnf(c_5919,plain,
    ( u1_pre_topc(k8_tmap_1(sK5,sK6)) = u1_pre_topc(sK5)
    | sK4(sK5,sK6) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_2757,c_5787])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_35])).

cnf(c_1294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X0,u1_pre_topc(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | k5_tmap_1(sK5,X0) != u1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_1293])).

cnf(c_1298,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X0,u1_pre_topc(sK5))
    | k5_tmap_1(sK5,X0) != u1_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1294,c_34,c_33])).

cnf(c_1935,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X0_54,u1_pre_topc(sK5))
    | k5_tmap_1(sK5,X0_54) != u1_pre_topc(sK5) ),
    inference(subtyping,[status(esa)],[c_1298])).

cnf(c_2773,plain,
    ( k5_tmap_1(sK5,X0_54) != u1_pre_topc(sK5)
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0_54,u1_pre_topc(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1935])).

cnf(c_4087,plain,
    ( u1_pre_topc(k8_tmap_1(sK5,sK6)) != u1_pre_topc(sK5)
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1952,c_2773])).

cnf(c_970,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_969])).

cnf(c_4690,plain,
    ( u1_pre_topc(k8_tmap_1(sK5,sK6)) != u1_pre_topc(sK5)
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4087,c_38,c_970])).

cnf(c_6896,plain,
    ( sK4(sK5,sK6) = u1_struct_0(sK6)
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5919,c_4690])).

cnf(c_28,negated_conjecture,
    ( ~ m1_pre_topc(sK6,sK5)
    | ~ v1_tsep_1(sK6,sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_293,plain,
    ( ~ v1_tsep_1(sK6,sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
    inference(prop_impl,[status(thm)],[c_31,c_28])).

cnf(c_706,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK4(X1,X0) = u1_struct_0(X0)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_293])).

cnf(c_707,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | ~ l1_pre_topc(sK5)
    | sK4(sK5,sK6) = u1_struct_0(sK6)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_709,plain,
    ( sK4(sK5,sK6) = u1_struct_0(sK6)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_33,c_31])).

cnf(c_1962,plain,
    ( sK4(sK5,sK6) = u1_struct_0(sK6)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_709])).

cnf(c_6898,plain,
    ( sK4(sK5,sK6) = u1_struct_0(sK6)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_5919,c_2817])).

cnf(c_6998,plain,
    ( sK4(sK5,sK6) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6896,c_1962,c_6898])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(sK4(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_717,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK4(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_293])).

cnf(c_718,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | ~ v3_pre_topc(sK4(sK5,sK6),sK5)
    | ~ l1_pre_topc(sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_720,plain,
    ( ~ v3_pre_topc(sK4(sK5,sK6),sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_718,c_33,c_31])).

cnf(c_1961,plain,
    ( ~ v3_pre_topc(sK4(sK5,sK6),sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_720])).

cnf(c_2750,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6)
    | v3_pre_topc(sK4(sK5,sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1961])).

cnf(c_7002,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6)
    | v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6998,c_2750])).

cnf(c_8720,plain,
    ( k8_tmap_1(sK5,sK5) != k8_tmap_1(sK5,sK6)
    | v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7002,c_7360])).

cnf(c_13,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1967,plain,
    ( v3_pre_topc(X0_54,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ r2_hidden(X0_54,u1_pre_topc(X0_53))
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3243,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_3244,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3243])).

cnf(c_3119,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5))
    | k5_tmap_1(sK5,u1_struct_0(sK6)) != u1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_1935])).

cnf(c_3120,plain,
    ( k5_tmap_1(sK5,u1_struct_0(sK6)) != u1_pre_topc(sK5)
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3119])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8907,c_8882,c_8720,c_3244,c_3120,c_970,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.45/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/1.00  
% 3.45/1.00  ------  iProver source info
% 3.45/1.00  
% 3.45/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.45/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/1.00  git: non_committed_changes: false
% 3.45/1.00  git: last_make_outside_of_git: false
% 3.45/1.00  
% 3.45/1.00  ------ 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options
% 3.45/1.00  
% 3.45/1.00  --out_options                           all
% 3.45/1.00  --tptp_safe_out                         true
% 3.45/1.00  --problem_path                          ""
% 3.45/1.00  --include_path                          ""
% 3.45/1.00  --clausifier                            res/vclausify_rel
% 3.45/1.00  --clausifier_options                    --mode clausify
% 3.45/1.00  --stdin                                 false
% 3.45/1.00  --stats_out                             all
% 3.45/1.00  
% 3.45/1.00  ------ General Options
% 3.45/1.00  
% 3.45/1.00  --fof                                   false
% 3.45/1.00  --time_out_real                         305.
% 3.45/1.00  --time_out_virtual                      -1.
% 3.45/1.00  --symbol_type_check                     false
% 3.45/1.00  --clausify_out                          false
% 3.45/1.00  --sig_cnt_out                           false
% 3.45/1.00  --trig_cnt_out                          false
% 3.45/1.00  --trig_cnt_out_tolerance                1.
% 3.45/1.00  --trig_cnt_out_sk_spl                   false
% 3.45/1.00  --abstr_cl_out                          false
% 3.45/1.00  
% 3.45/1.00  ------ Global Options
% 3.45/1.00  
% 3.45/1.00  --schedule                              default
% 3.45/1.00  --add_important_lit                     false
% 3.45/1.00  --prop_solver_per_cl                    1000
% 3.45/1.00  --min_unsat_core                        false
% 3.45/1.00  --soft_assumptions                      false
% 3.45/1.00  --soft_lemma_size                       3
% 3.45/1.00  --prop_impl_unit_size                   0
% 3.45/1.00  --prop_impl_unit                        []
% 3.45/1.00  --share_sel_clauses                     true
% 3.45/1.00  --reset_solvers                         false
% 3.45/1.00  --bc_imp_inh                            [conj_cone]
% 3.45/1.00  --conj_cone_tolerance                   3.
% 3.45/1.00  --extra_neg_conj                        none
% 3.45/1.00  --large_theory_mode                     true
% 3.45/1.00  --prolific_symb_bound                   200
% 3.45/1.00  --lt_threshold                          2000
% 3.45/1.00  --clause_weak_htbl                      true
% 3.45/1.00  --gc_record_bc_elim                     false
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing Options
% 3.45/1.00  
% 3.45/1.00  --preprocessing_flag                    true
% 3.45/1.00  --time_out_prep_mult                    0.1
% 3.45/1.00  --splitting_mode                        input
% 3.45/1.00  --splitting_grd                         true
% 3.45/1.00  --splitting_cvd                         false
% 3.45/1.00  --splitting_cvd_svl                     false
% 3.45/1.00  --splitting_nvd                         32
% 3.45/1.00  --sub_typing                            true
% 3.45/1.00  --prep_gs_sim                           true
% 3.45/1.00  --prep_unflatten                        true
% 3.45/1.00  --prep_res_sim                          true
% 3.45/1.00  --prep_upred                            true
% 3.45/1.00  --prep_sem_filter                       exhaustive
% 3.45/1.00  --prep_sem_filter_out                   false
% 3.45/1.00  --pred_elim                             true
% 3.45/1.00  --res_sim_input                         true
% 3.45/1.00  --eq_ax_congr_red                       true
% 3.45/1.00  --pure_diseq_elim                       true
% 3.45/1.00  --brand_transform                       false
% 3.45/1.00  --non_eq_to_eq                          false
% 3.45/1.00  --prep_def_merge                        true
% 3.45/1.00  --prep_def_merge_prop_impl              false
% 3.45/1.00  --prep_def_merge_mbd                    true
% 3.45/1.00  --prep_def_merge_tr_red                 false
% 3.45/1.00  --prep_def_merge_tr_cl                  false
% 3.45/1.00  --smt_preprocessing                     true
% 3.45/1.00  --smt_ac_axioms                         fast
% 3.45/1.00  --preprocessed_out                      false
% 3.45/1.00  --preprocessed_stats                    false
% 3.45/1.00  
% 3.45/1.00  ------ Abstraction refinement Options
% 3.45/1.00  
% 3.45/1.00  --abstr_ref                             []
% 3.45/1.00  --abstr_ref_prep                        false
% 3.45/1.00  --abstr_ref_until_sat                   false
% 3.45/1.00  --abstr_ref_sig_restrict                funpre
% 3.45/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/1.00  --abstr_ref_under                       []
% 3.45/1.00  
% 3.45/1.00  ------ SAT Options
% 3.45/1.00  
% 3.45/1.00  --sat_mode                              false
% 3.45/1.00  --sat_fm_restart_options                ""
% 3.45/1.00  --sat_gr_def                            false
% 3.45/1.00  --sat_epr_types                         true
% 3.45/1.00  --sat_non_cyclic_types                  false
% 3.45/1.00  --sat_finite_models                     false
% 3.45/1.00  --sat_fm_lemmas                         false
% 3.45/1.00  --sat_fm_prep                           false
% 3.45/1.00  --sat_fm_uc_incr                        true
% 3.45/1.00  --sat_out_model                         small
% 3.45/1.00  --sat_out_clauses                       false
% 3.45/1.00  
% 3.45/1.00  ------ QBF Options
% 3.45/1.00  
% 3.45/1.00  --qbf_mode                              false
% 3.45/1.00  --qbf_elim_univ                         false
% 3.45/1.00  --qbf_dom_inst                          none
% 3.45/1.00  --qbf_dom_pre_inst                      false
% 3.45/1.00  --qbf_sk_in                             false
% 3.45/1.00  --qbf_pred_elim                         true
% 3.45/1.00  --qbf_split                             512
% 3.45/1.00  
% 3.45/1.00  ------ BMC1 Options
% 3.45/1.00  
% 3.45/1.00  --bmc1_incremental                      false
% 3.45/1.00  --bmc1_axioms                           reachable_all
% 3.45/1.00  --bmc1_min_bound                        0
% 3.45/1.00  --bmc1_max_bound                        -1
% 3.45/1.00  --bmc1_max_bound_default                -1
% 3.45/1.00  --bmc1_symbol_reachability              true
% 3.45/1.00  --bmc1_property_lemmas                  false
% 3.45/1.00  --bmc1_k_induction                      false
% 3.45/1.00  --bmc1_non_equiv_states                 false
% 3.45/1.00  --bmc1_deadlock                         false
% 3.45/1.00  --bmc1_ucm                              false
% 3.45/1.00  --bmc1_add_unsat_core                   none
% 3.45/1.00  --bmc1_unsat_core_children              false
% 3.45/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/1.00  --bmc1_out_stat                         full
% 3.45/1.00  --bmc1_ground_init                      false
% 3.45/1.00  --bmc1_pre_inst_next_state              false
% 3.45/1.00  --bmc1_pre_inst_state                   false
% 3.45/1.00  --bmc1_pre_inst_reach_state             false
% 3.45/1.00  --bmc1_out_unsat_core                   false
% 3.45/1.00  --bmc1_aig_witness_out                  false
% 3.45/1.00  --bmc1_verbose                          false
% 3.45/1.00  --bmc1_dump_clauses_tptp                false
% 3.45/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.45/1.00  --bmc1_dump_file                        -
% 3.45/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.45/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.45/1.00  --bmc1_ucm_extend_mode                  1
% 3.45/1.00  --bmc1_ucm_init_mode                    2
% 3.45/1.00  --bmc1_ucm_cone_mode                    none
% 3.45/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.45/1.00  --bmc1_ucm_relax_model                  4
% 3.45/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.45/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/1.00  --bmc1_ucm_layered_model                none
% 3.45/1.00  --bmc1_ucm_max_lemma_size               10
% 3.45/1.00  
% 3.45/1.00  ------ AIG Options
% 3.45/1.00  
% 3.45/1.00  --aig_mode                              false
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation Options
% 3.45/1.00  
% 3.45/1.00  --instantiation_flag                    true
% 3.45/1.00  --inst_sos_flag                         false
% 3.45/1.00  --inst_sos_phase                        true
% 3.45/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel_side                     num_symb
% 3.45/1.00  --inst_solver_per_active                1400
% 3.45/1.00  --inst_solver_calls_frac                1.
% 3.45/1.00  --inst_passive_queue_type               priority_queues
% 3.45/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/1.00  --inst_passive_queues_freq              [25;2]
% 3.45/1.00  --inst_dismatching                      true
% 3.45/1.00  --inst_eager_unprocessed_to_passive     true
% 3.45/1.00  --inst_prop_sim_given                   true
% 3.45/1.00  --inst_prop_sim_new                     false
% 3.45/1.00  --inst_subs_new                         false
% 3.45/1.00  --inst_eq_res_simp                      false
% 3.45/1.00  --inst_subs_given                       false
% 3.45/1.00  --inst_orphan_elimination               true
% 3.45/1.00  --inst_learning_loop_flag               true
% 3.45/1.00  --inst_learning_start                   3000
% 3.45/1.00  --inst_learning_factor                  2
% 3.45/1.00  --inst_start_prop_sim_after_learn       3
% 3.45/1.00  --inst_sel_renew                        solver
% 3.45/1.00  --inst_lit_activity_flag                true
% 3.45/1.00  --inst_restr_to_given                   false
% 3.45/1.00  --inst_activity_threshold               500
% 3.45/1.00  --inst_out_proof                        true
% 3.45/1.00  
% 3.45/1.00  ------ Resolution Options
% 3.45/1.00  
% 3.45/1.00  --resolution_flag                       true
% 3.45/1.00  --res_lit_sel                           adaptive
% 3.45/1.00  --res_lit_sel_side                      none
% 3.45/1.00  --res_ordering                          kbo
% 3.45/1.00  --res_to_prop_solver                    active
% 3.45/1.00  --res_prop_simpl_new                    false
% 3.45/1.00  --res_prop_simpl_given                  true
% 3.45/1.00  --res_passive_queue_type                priority_queues
% 3.45/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/1.00  --res_passive_queues_freq               [15;5]
% 3.45/1.00  --res_forward_subs                      full
% 3.45/1.00  --res_backward_subs                     full
% 3.45/1.00  --res_forward_subs_resolution           true
% 3.45/1.00  --res_backward_subs_resolution          true
% 3.45/1.00  --res_orphan_elimination                true
% 3.45/1.00  --res_time_limit                        2.
% 3.45/1.00  --res_out_proof                         true
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Options
% 3.45/1.00  
% 3.45/1.00  --superposition_flag                    true
% 3.45/1.00  --sup_passive_queue_type                priority_queues
% 3.45/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.45/1.00  --demod_completeness_check              fast
% 3.45/1.00  --demod_use_ground                      true
% 3.45/1.00  --sup_to_prop_solver                    passive
% 3.45/1.00  --sup_prop_simpl_new                    true
% 3.45/1.00  --sup_prop_simpl_given                  true
% 3.45/1.00  --sup_fun_splitting                     false
% 3.45/1.00  --sup_smt_interval                      50000
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Simplification Setup
% 3.45/1.00  
% 3.45/1.00  --sup_indices_passive                   []
% 3.45/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_full_bw                           [BwDemod]
% 3.45/1.00  --sup_immed_triv                        [TrivRules]
% 3.45/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_immed_bw_main                     []
% 3.45/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  
% 3.45/1.00  ------ Combination Options
% 3.45/1.00  
% 3.45/1.00  --comb_res_mult                         3
% 3.45/1.00  --comb_sup_mult                         2
% 3.45/1.00  --comb_inst_mult                        10
% 3.45/1.00  
% 3.45/1.00  ------ Debug Options
% 3.45/1.00  
% 3.45/1.00  --dbg_backtrace                         false
% 3.45/1.00  --dbg_dump_prop_clauses                 false
% 3.45/1.00  --dbg_dump_prop_clauses_file            -
% 3.45/1.00  --dbg_out_stat                          false
% 3.45/1.00  ------ Parsing...
% 3.45/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/1.00  ------ Proving...
% 3.45/1.00  ------ Problem Properties 
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  clauses                                 49
% 3.45/1.00  conjectures                             2
% 3.45/1.00  EPR                                     5
% 3.45/1.00  Horn                                    38
% 3.45/1.00  unary                                   13
% 3.45/1.00  binary                                  13
% 3.45/1.00  lits                                    123
% 3.45/1.00  lits eq                                 20
% 3.45/1.00  fd_pure                                 0
% 3.45/1.00  fd_pseudo                               0
% 3.45/1.00  fd_cond                                 0
% 3.45/1.00  fd_pseudo_cond                          0
% 3.45/1.00  AC symbols                              0
% 3.45/1.00  
% 3.45/1.00  ------ Schedule dynamic 5 is on 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  ------ 
% 3.45/1.00  Current options:
% 3.45/1.00  ------ 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options
% 3.45/1.00  
% 3.45/1.00  --out_options                           all
% 3.45/1.00  --tptp_safe_out                         true
% 3.45/1.00  --problem_path                          ""
% 3.45/1.00  --include_path                          ""
% 3.45/1.00  --clausifier                            res/vclausify_rel
% 3.45/1.00  --clausifier_options                    --mode clausify
% 3.45/1.00  --stdin                                 false
% 3.45/1.00  --stats_out                             all
% 3.45/1.00  
% 3.45/1.00  ------ General Options
% 3.45/1.00  
% 3.45/1.00  --fof                                   false
% 3.45/1.00  --time_out_real                         305.
% 3.45/1.00  --time_out_virtual                      -1.
% 3.45/1.00  --symbol_type_check                     false
% 3.45/1.00  --clausify_out                          false
% 3.45/1.00  --sig_cnt_out                           false
% 3.45/1.00  --trig_cnt_out                          false
% 3.45/1.00  --trig_cnt_out_tolerance                1.
% 3.45/1.00  --trig_cnt_out_sk_spl                   false
% 3.45/1.00  --abstr_cl_out                          false
% 3.45/1.00  
% 3.45/1.00  ------ Global Options
% 3.45/1.00  
% 3.45/1.00  --schedule                              default
% 3.45/1.00  --add_important_lit                     false
% 3.45/1.00  --prop_solver_per_cl                    1000
% 3.45/1.00  --min_unsat_core                        false
% 3.45/1.00  --soft_assumptions                      false
% 3.45/1.00  --soft_lemma_size                       3
% 3.45/1.00  --prop_impl_unit_size                   0
% 3.45/1.00  --prop_impl_unit                        []
% 3.45/1.00  --share_sel_clauses                     true
% 3.45/1.00  --reset_solvers                         false
% 3.45/1.00  --bc_imp_inh                            [conj_cone]
% 3.45/1.00  --conj_cone_tolerance                   3.
% 3.45/1.00  --extra_neg_conj                        none
% 3.45/1.00  --large_theory_mode                     true
% 3.45/1.00  --prolific_symb_bound                   200
% 3.45/1.00  --lt_threshold                          2000
% 3.45/1.00  --clause_weak_htbl                      true
% 3.45/1.00  --gc_record_bc_elim                     false
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing Options
% 3.45/1.00  
% 3.45/1.00  --preprocessing_flag                    true
% 3.45/1.00  --time_out_prep_mult                    0.1
% 3.45/1.00  --splitting_mode                        input
% 3.45/1.00  --splitting_grd                         true
% 3.45/1.00  --splitting_cvd                         false
% 3.45/1.00  --splitting_cvd_svl                     false
% 3.45/1.00  --splitting_nvd                         32
% 3.45/1.00  --sub_typing                            true
% 3.45/1.00  --prep_gs_sim                           true
% 3.45/1.00  --prep_unflatten                        true
% 3.45/1.00  --prep_res_sim                          true
% 3.45/1.00  --prep_upred                            true
% 3.45/1.00  --prep_sem_filter                       exhaustive
% 3.45/1.00  --prep_sem_filter_out                   false
% 3.45/1.00  --pred_elim                             true
% 3.45/1.00  --res_sim_input                         true
% 3.45/1.00  --eq_ax_congr_red                       true
% 3.45/1.00  --pure_diseq_elim                       true
% 3.45/1.00  --brand_transform                       false
% 3.45/1.00  --non_eq_to_eq                          false
% 3.45/1.00  --prep_def_merge                        true
% 3.45/1.00  --prep_def_merge_prop_impl              false
% 3.45/1.00  --prep_def_merge_mbd                    true
% 3.45/1.00  --prep_def_merge_tr_red                 false
% 3.45/1.00  --prep_def_merge_tr_cl                  false
% 3.45/1.00  --smt_preprocessing                     true
% 3.45/1.00  --smt_ac_axioms                         fast
% 3.45/1.00  --preprocessed_out                      false
% 3.45/1.00  --preprocessed_stats                    false
% 3.45/1.00  
% 3.45/1.00  ------ Abstraction refinement Options
% 3.45/1.00  
% 3.45/1.00  --abstr_ref                             []
% 3.45/1.00  --abstr_ref_prep                        false
% 3.45/1.00  --abstr_ref_until_sat                   false
% 3.45/1.00  --abstr_ref_sig_restrict                funpre
% 3.45/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/1.00  --abstr_ref_under                       []
% 3.45/1.00  
% 3.45/1.00  ------ SAT Options
% 3.45/1.00  
% 3.45/1.00  --sat_mode                              false
% 3.45/1.00  --sat_fm_restart_options                ""
% 3.45/1.00  --sat_gr_def                            false
% 3.45/1.00  --sat_epr_types                         true
% 3.45/1.00  --sat_non_cyclic_types                  false
% 3.45/1.00  --sat_finite_models                     false
% 3.45/1.00  --sat_fm_lemmas                         false
% 3.45/1.00  --sat_fm_prep                           false
% 3.45/1.00  --sat_fm_uc_incr                        true
% 3.45/1.00  --sat_out_model                         small
% 3.45/1.00  --sat_out_clauses                       false
% 3.45/1.00  
% 3.45/1.00  ------ QBF Options
% 3.45/1.00  
% 3.45/1.00  --qbf_mode                              false
% 3.45/1.00  --qbf_elim_univ                         false
% 3.45/1.00  --qbf_dom_inst                          none
% 3.45/1.00  --qbf_dom_pre_inst                      false
% 3.45/1.00  --qbf_sk_in                             false
% 3.45/1.00  --qbf_pred_elim                         true
% 3.45/1.00  --qbf_split                             512
% 3.45/1.00  
% 3.45/1.00  ------ BMC1 Options
% 3.45/1.00  
% 3.45/1.00  --bmc1_incremental                      false
% 3.45/1.00  --bmc1_axioms                           reachable_all
% 3.45/1.00  --bmc1_min_bound                        0
% 3.45/1.00  --bmc1_max_bound                        -1
% 3.45/1.00  --bmc1_max_bound_default                -1
% 3.45/1.00  --bmc1_symbol_reachability              true
% 3.45/1.00  --bmc1_property_lemmas                  false
% 3.45/1.00  --bmc1_k_induction                      false
% 3.45/1.00  --bmc1_non_equiv_states                 false
% 3.45/1.00  --bmc1_deadlock                         false
% 3.45/1.00  --bmc1_ucm                              false
% 3.45/1.00  --bmc1_add_unsat_core                   none
% 3.45/1.00  --bmc1_unsat_core_children              false
% 3.45/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/1.00  --bmc1_out_stat                         full
% 3.45/1.00  --bmc1_ground_init                      false
% 3.45/1.00  --bmc1_pre_inst_next_state              false
% 3.45/1.00  --bmc1_pre_inst_state                   false
% 3.45/1.00  --bmc1_pre_inst_reach_state             false
% 3.45/1.00  --bmc1_out_unsat_core                   false
% 3.45/1.00  --bmc1_aig_witness_out                  false
% 3.45/1.00  --bmc1_verbose                          false
% 3.45/1.00  --bmc1_dump_clauses_tptp                false
% 3.45/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.45/1.00  --bmc1_dump_file                        -
% 3.45/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.45/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.45/1.00  --bmc1_ucm_extend_mode                  1
% 3.45/1.00  --bmc1_ucm_init_mode                    2
% 3.45/1.00  --bmc1_ucm_cone_mode                    none
% 3.45/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.45/1.00  --bmc1_ucm_relax_model                  4
% 3.45/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.45/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/1.00  --bmc1_ucm_layered_model                none
% 3.45/1.00  --bmc1_ucm_max_lemma_size               10
% 3.45/1.00  
% 3.45/1.00  ------ AIG Options
% 3.45/1.00  
% 3.45/1.00  --aig_mode                              false
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation Options
% 3.45/1.00  
% 3.45/1.00  --instantiation_flag                    true
% 3.45/1.00  --inst_sos_flag                         false
% 3.45/1.00  --inst_sos_phase                        true
% 3.45/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel_side                     none
% 3.45/1.00  --inst_solver_per_active                1400
% 3.45/1.00  --inst_solver_calls_frac                1.
% 3.45/1.00  --inst_passive_queue_type               priority_queues
% 3.45/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/1.00  --inst_passive_queues_freq              [25;2]
% 3.45/1.00  --inst_dismatching                      true
% 3.45/1.00  --inst_eager_unprocessed_to_passive     true
% 3.45/1.00  --inst_prop_sim_given                   true
% 3.45/1.00  --inst_prop_sim_new                     false
% 3.45/1.00  --inst_subs_new                         false
% 3.45/1.00  --inst_eq_res_simp                      false
% 3.45/1.00  --inst_subs_given                       false
% 3.45/1.00  --inst_orphan_elimination               true
% 3.45/1.00  --inst_learning_loop_flag               true
% 3.45/1.00  --inst_learning_start                   3000
% 3.45/1.00  --inst_learning_factor                  2
% 3.45/1.00  --inst_start_prop_sim_after_learn       3
% 3.45/1.00  --inst_sel_renew                        solver
% 3.45/1.00  --inst_lit_activity_flag                true
% 3.45/1.00  --inst_restr_to_given                   false
% 3.45/1.00  --inst_activity_threshold               500
% 3.45/1.00  --inst_out_proof                        true
% 3.45/1.00  
% 3.45/1.00  ------ Resolution Options
% 3.45/1.00  
% 3.45/1.00  --resolution_flag                       false
% 3.45/1.00  --res_lit_sel                           adaptive
% 3.45/1.00  --res_lit_sel_side                      none
% 3.45/1.00  --res_ordering                          kbo
% 3.45/1.00  --res_to_prop_solver                    active
% 3.45/1.00  --res_prop_simpl_new                    false
% 3.45/1.00  --res_prop_simpl_given                  true
% 3.45/1.00  --res_passive_queue_type                priority_queues
% 3.45/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/1.00  --res_passive_queues_freq               [15;5]
% 3.45/1.00  --res_forward_subs                      full
% 3.45/1.00  --res_backward_subs                     full
% 3.45/1.00  --res_forward_subs_resolution           true
% 3.45/1.00  --res_backward_subs_resolution          true
% 3.45/1.00  --res_orphan_elimination                true
% 3.45/1.00  --res_time_limit                        2.
% 3.45/1.00  --res_out_proof                         true
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Options
% 3.45/1.00  
% 3.45/1.00  --superposition_flag                    true
% 3.45/1.00  --sup_passive_queue_type                priority_queues
% 3.45/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.45/1.00  --demod_completeness_check              fast
% 3.45/1.00  --demod_use_ground                      true
% 3.45/1.00  --sup_to_prop_solver                    passive
% 3.45/1.00  --sup_prop_simpl_new                    true
% 3.45/1.00  --sup_prop_simpl_given                  true
% 3.45/1.00  --sup_fun_splitting                     false
% 3.45/1.00  --sup_smt_interval                      50000
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Simplification Setup
% 3.45/1.00  
% 3.45/1.00  --sup_indices_passive                   []
% 3.45/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_full_bw                           [BwDemod]
% 3.45/1.00  --sup_immed_triv                        [TrivRules]
% 3.45/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_immed_bw_main                     []
% 3.45/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  
% 3.45/1.00  ------ Combination Options
% 3.45/1.00  
% 3.45/1.00  --comb_res_mult                         3
% 3.45/1.00  --comb_sup_mult                         2
% 3.45/1.00  --comb_inst_mult                        10
% 3.45/1.00  
% 3.45/1.00  ------ Debug Options
% 3.45/1.00  
% 3.45/1.00  --dbg_backtrace                         false
% 3.45/1.00  --dbg_dump_prop_clauses                 false
% 3.45/1.00  --dbg_dump_prop_clauses_file            -
% 3.45/1.00  --dbg_out_stat                          false
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  ------ Proving...
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  % SZS status Theorem for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  fof(f4,axiom,(
% 3.45/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f18,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f4])).
% 3.45/1.00  
% 3.45/1.00  fof(f19,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(flattening,[],[f18])).
% 3.45/1.00  
% 3.45/1.00  fof(f43,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(nnf_transformation,[],[f19])).
% 3.45/1.00  
% 3.45/1.00  fof(f44,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(rectify,[],[f43])).
% 3.45/1.00  
% 3.45/1.00  fof(f45,plain,(
% 3.45/1.00    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0,X1),X0) & u1_struct_0(X1) = sK4(X0,X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f46,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK4(X0,X1),X0) & u1_struct_0(X1) = sK4(X0,X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).
% 3.45/1.00  
% 3.45/1.00  fof(f68,plain,(
% 3.45/1.00    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f46])).
% 3.45/1.00  
% 3.45/1.00  fof(f89,plain,(
% 3.45/1.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(equality_resolution,[],[f68])).
% 3.45/1.00  
% 3.45/1.00  fof(f8,axiom,(
% 3.45/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f26,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f8])).
% 3.45/1.00  
% 3.45/1.00  fof(f79,plain,(
% 3.45/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f26])).
% 3.45/1.00  
% 3.45/1.00  fof(f10,conjecture,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f11,negated_conjecture,(
% 3.45/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 3.45/1.00    inference(negated_conjecture,[],[f10])).
% 3.45/1.00  
% 3.45/1.00  fof(f28,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f11])).
% 3.45/1.00  
% 3.45/1.00  fof(f29,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.45/1.00    inference(flattening,[],[f28])).
% 3.45/1.00  
% 3.45/1.00  fof(f48,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.45/1.00    inference(nnf_transformation,[],[f29])).
% 3.45/1.00  
% 3.45/1.00  fof(f49,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.45/1.00    inference(flattening,[],[f48])).
% 3.45/1.00  
% 3.45/1.00  fof(f51,plain,(
% 3.45/1.00    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK6) | ~m1_pre_topc(sK6,X0) | ~v1_tsep_1(sK6,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK6) | (m1_pre_topc(sK6,X0) & v1_tsep_1(sK6,X0))) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f50,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,X1) | ~m1_pre_topc(X1,sK5) | ~v1_tsep_1(X1,sK5)) & (g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,X1) | (m1_pre_topc(X1,sK5) & v1_tsep_1(X1,sK5))) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f52,plain,(
% 3.45/1.00    ((g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) | ~m1_pre_topc(sK6,sK5) | ~v1_tsep_1(sK6,sK5)) & (g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) | (m1_pre_topc(sK6,sK5) & v1_tsep_1(sK6,sK5))) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f49,f51,f50])).
% 3.45/1.00  
% 3.45/1.00  fof(f86,plain,(
% 3.45/1.00    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) | v1_tsep_1(sK6,sK5)),
% 3.45/1.00    inference(cnf_transformation,[],[f52])).
% 3.45/1.00  
% 3.45/1.00  fof(f83,plain,(
% 3.45/1.00    l1_pre_topc(sK5)),
% 3.45/1.00    inference(cnf_transformation,[],[f52])).
% 3.45/1.00  
% 3.45/1.00  fof(f85,plain,(
% 3.45/1.00    m1_pre_topc(sK6,sK5)),
% 3.45/1.00    inference(cnf_transformation,[],[f52])).
% 3.45/1.00  
% 3.45/1.00  fof(f87,plain,(
% 3.45/1.00    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) | m1_pre_topc(sK6,sK5)),
% 3.45/1.00    inference(cnf_transformation,[],[f52])).
% 3.45/1.00  
% 3.45/1.00  fof(f3,axiom,(
% 3.45/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f17,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f3])).
% 3.45/1.00  
% 3.45/1.00  fof(f42,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(nnf_transformation,[],[f17])).
% 3.45/1.00  
% 3.45/1.00  fof(f66,plain,(
% 3.45/1.00    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f42])).
% 3.45/1.00  
% 3.45/1.00  fof(f6,axiom,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f22,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f6])).
% 3.45/1.00  
% 3.45/1.00  fof(f23,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.00    inference(flattening,[],[f22])).
% 3.45/1.00  
% 3.45/1.00  fof(f47,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.00    inference(nnf_transformation,[],[f23])).
% 3.45/1.00  
% 3.45/1.00  fof(f75,plain,(
% 3.45/1.00    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f47])).
% 3.45/1.00  
% 3.45/1.00  fof(f81,plain,(
% 3.45/1.00    ~v2_struct_0(sK5)),
% 3.45/1.00    inference(cnf_transformation,[],[f52])).
% 3.45/1.00  
% 3.45/1.00  fof(f82,plain,(
% 3.45/1.00    v2_pre_topc(sK5)),
% 3.45/1.00    inference(cnf_transformation,[],[f52])).
% 3.45/1.00  
% 3.45/1.00  fof(f7,axiom,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f24,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f7])).
% 3.45/1.00  
% 3.45/1.00  fof(f25,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.00    inference(flattening,[],[f24])).
% 3.45/1.00  
% 3.45/1.00  fof(f78,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f25])).
% 3.45/1.00  
% 3.45/1.00  fof(f90,plain,(
% 3.45/1.00    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(equality_resolution,[],[f78])).
% 3.45/1.00  
% 3.45/1.00  fof(f84,plain,(
% 3.45/1.00    ~v2_struct_0(sK6)),
% 3.45/1.00    inference(cnf_transformation,[],[f52])).
% 3.45/1.00  
% 3.45/1.00  fof(f77,plain,(
% 3.45/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f25])).
% 3.45/1.00  
% 3.45/1.00  fof(f9,axiom,(
% 3.45/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f27,plain,(
% 3.45/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f9])).
% 3.45/1.00  
% 3.45/1.00  fof(f80,plain,(
% 3.45/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f27])).
% 3.45/1.00  
% 3.45/1.00  fof(f2,axiom,(
% 3.45/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f12,plain,(
% 3.45/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.45/1.00    inference(rectify,[],[f2])).
% 3.45/1.00  
% 3.45/1.00  fof(f15,plain,(
% 3.45/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f12])).
% 3.45/1.00  
% 3.45/1.00  fof(f16,plain,(
% 3.45/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(flattening,[],[f15])).
% 3.45/1.00  
% 3.45/1.00  fof(f30,plain,(
% 3.45/1.00    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.45/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.45/1.00  
% 3.45/1.00  fof(f31,plain,(
% 3.45/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(definition_folding,[],[f16,f30])).
% 3.45/1.00  
% 3.45/1.00  fof(f37,plain,(
% 3.45/1.00    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(nnf_transformation,[],[f31])).
% 3.45/1.00  
% 3.45/1.00  fof(f38,plain,(
% 3.45/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(flattening,[],[f37])).
% 3.45/1.00  
% 3.45/1.00  fof(f39,plain,(
% 3.45/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(rectify,[],[f38])).
% 3.45/1.00  
% 3.45/1.00  fof(f40,plain,(
% 3.45/1.00    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f41,plain,(
% 3.45/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 3.45/1.00  
% 3.45/1.00  fof(f60,plain,(
% 3.45/1.00    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f41])).
% 3.45/1.00  
% 3.45/1.00  fof(f1,axiom,(
% 3.45/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f13,plain,(
% 3.45/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f1])).
% 3.45/1.00  
% 3.45/1.00  fof(f14,plain,(
% 3.45/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.45/1.00    inference(flattening,[],[f13])).
% 3.45/1.00  
% 3.45/1.00  fof(f53,plain,(
% 3.45/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f14])).
% 3.45/1.00  
% 3.45/1.00  fof(f5,axiom,(
% 3.45/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f20,plain,(
% 3.45/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f5])).
% 3.45/1.00  
% 3.45/1.00  fof(f21,plain,(
% 3.45/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.00    inference(flattening,[],[f20])).
% 3.45/1.00  
% 3.45/1.00  fof(f72,plain,(
% 3.45/1.00    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f21])).
% 3.45/1.00  
% 3.45/1.00  fof(f74,plain,(
% 3.45/1.00    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f21])).
% 3.45/1.00  
% 3.45/1.00  fof(f70,plain,(
% 3.45/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK4(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f46])).
% 3.45/1.00  
% 3.45/1.00  fof(f76,plain,(
% 3.45/1.00    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f47])).
% 3.45/1.00  
% 3.45/1.00  fof(f88,plain,(
% 3.45/1.00    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) | ~m1_pre_topc(sK6,sK5) | ~v1_tsep_1(sK6,sK5)),
% 3.45/1.00    inference(cnf_transformation,[],[f52])).
% 3.45/1.00  
% 3.45/1.00  fof(f71,plain,(
% 3.45/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK4(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f46])).
% 3.45/1.00  
% 3.45/1.00  fof(f67,plain,(
% 3.45/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f42])).
% 3.45/1.00  
% 3.45/1.00  cnf(c_18,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | ~ v1_tsep_1(X0,X1)
% 3.45/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.45/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_26,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_226,plain,
% 3.45/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.45/1.00      | ~ v1_tsep_1(X0,X1)
% 3.45/1.00      | ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_18,c_26]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_227,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | ~ v1_tsep_1(X0,X1)
% 3.45/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_226]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_30,negated_conjecture,
% 3.45/1.00      ( v1_tsep_1(sK6,sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_295,plain,
% 3.45/1.00      ( v1_tsep_1(sK6,sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(prop_impl,[status(thm)],[c_30]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_731,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6)
% 3.45/1.00      | sK6 != X0
% 3.45/1.00      | sK5 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_227,c_295]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_732,plain,
% 3.45/1.00      ( ~ m1_pre_topc(sK6,sK5)
% 3.45/1.00      | v3_pre_topc(u1_struct_0(sK6),sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_731]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_33,negated_conjecture,
% 3.45/1.00      ( l1_pre_topc(sK5) ),
% 3.45/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_31,negated_conjecture,
% 3.45/1.00      ( m1_pre_topc(sK6,sK5) ),
% 3.45/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_734,plain,
% 3.45/1.00      ( v3_pre_topc(u1_struct_0(sK6),sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_732,c_33,c_31]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1960,plain,
% 3.45/1.00      ( v3_pre_topc(u1_struct_0(sK6),sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_734]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2751,plain,
% 3.45/1.00      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6)
% 3.45/1.00      | v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1960]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_29,negated_conjecture,
% 3.45/1.00      ( m1_pre_topc(sK6,sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_201,negated_conjecture,
% 3.45/1.00      ( m1_pre_topc(sK6,sK5) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_29,c_31]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_968,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | sK6 != X0
% 3.45/1.00      | sK5 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_201]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_969,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.45/1.00      | ~ l1_pre_topc(sK5) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_968]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_971,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_969,c_33]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1951,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_971]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2759,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1951]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_14,plain,
% 3.45/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1966,plain,
% 3.45/1.00      ( ~ v3_pre_topc(X0_54,X0_53)
% 3.45/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.45/1.00      | r2_hidden(X0_54,u1_pre_topc(X0_53))
% 3.45/1.00      | ~ l1_pre_topc(X0_53) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2746,plain,
% 3.45/1.00      ( v3_pre_topc(X0_54,X0_53) != iProver_top
% 3.45/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53))) != iProver_top
% 3.45/1.00      | r2_hidden(X0_54,u1_pre_topc(X0_53)) = iProver_top
% 3.45/1.00      | l1_pre_topc(X0_53) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1966]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3746,plain,
% 3.45/1.00      ( v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top
% 3.45/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top
% 3.45/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_2759,c_2746]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_38,plain,
% 3.45/1.00      ( l1_pre_topc(sK5) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5780,plain,
% 3.45/1.00      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top
% 3.45/1.00      | v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3746,c_38]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5781,plain,
% 3.45/1.00      ( v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top
% 3.45/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_5780]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_23,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_35,negated_conjecture,
% 3.45/1.00      ( ~ v2_struct_0(sK5) ),
% 3.45/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1272,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 3.45/1.00      | sK5 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1273,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.45/1.00      | ~ r2_hidden(X0,u1_pre_topc(sK5))
% 3.45/1.00      | ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | k5_tmap_1(sK5,X0) = u1_pre_topc(sK5) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1272]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_34,negated_conjecture,
% 3.45/1.00      ( v2_pre_topc(sK5) ),
% 3.45/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1277,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.45/1.00      | ~ r2_hidden(X0,u1_pre_topc(sK5))
% 3.45/1.00      | k5_tmap_1(sK5,X0) = u1_pre_topc(sK5) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1273,c_34,c_33]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1936,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.45/1.00      | ~ r2_hidden(X0_54,u1_pre_topc(sK5))
% 3.45/1.00      | k5_tmap_1(sK5,X0_54) = u1_pre_topc(sK5) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_1277]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2772,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,X0_54) = u1_pre_topc(sK5)
% 3.45/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.45/1.00      | r2_hidden(X0_54,u1_pre_topc(sK5)) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1936]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3979,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(sK5)
% 3.45/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_2759,c_2772]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_24,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | v2_struct_0(X0)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_214,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | v2_struct_0(X0)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_24,c_26]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_215,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v2_struct_0(X0)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_214]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_960,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0))
% 3.45/1.00      | sK6 != X0
% 3.45/1.00      | sK5 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_215,c_201]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_961,plain,
% 3.45/1.00      ( v2_struct_0(sK6)
% 3.45/1.00      | v2_struct_0(sK5)
% 3.45/1.00      | ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(k8_tmap_1(sK5,sK6)) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_960]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_32,negated_conjecture,
% 3.45/1.00      ( ~ v2_struct_0(sK6) ),
% 3.45/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_963,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(k8_tmap_1(sK5,sK6)) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_961,c_35,c_34,c_33,c_32]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1952,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(k8_tmap_1(sK5,sK6)) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_963]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3984,plain,
% 3.45/1.00      ( u1_pre_topc(k8_tmap_1(sK5,sK6)) = u1_pre_topc(sK5)
% 3.45/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_3979,c_1952]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5787,plain,
% 3.45/1.00      ( u1_pre_topc(k8_tmap_1(sK5,sK6)) = u1_pre_topc(sK5)
% 3.45/1.00      | v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5781,c_3984]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6115,plain,
% 3.45/1.00      ( u1_pre_topc(k8_tmap_1(sK5,sK6)) = u1_pre_topc(sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_2751,c_5787]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_25,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | v2_struct_0(X0)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_27,plain,
% 3.45/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_846,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X2)
% 3.45/1.00      | X2 != X1
% 3.45/1.00      | X2 != X0
% 3.45/1.00      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_847,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | ~ v2_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0)
% 3.45/1.00      | u1_struct_0(k8_tmap_1(X0,X0)) = u1_struct_0(X0) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_846]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1214,plain,
% 3.45/1.00      ( ~ v2_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0)
% 3.45/1.00      | u1_struct_0(k8_tmap_1(X0,X0)) = u1_struct_0(X0)
% 3.45/1.00      | sK5 != X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_847,c_35]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1215,plain,
% 3.45/1.00      ( ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | u1_struct_0(k8_tmap_1(sK5,sK5)) = u1_struct_0(sK5) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1214]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_45,plain,
% 3.45/1.00      ( m1_pre_topc(sK5,sK5) | ~ l1_pre_topc(sK5) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_51,plain,
% 3.45/1.00      ( ~ m1_pre_topc(sK5,sK5)
% 3.45/1.00      | v2_struct_0(sK5)
% 3.45/1.00      | ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | u1_struct_0(k8_tmap_1(sK5,sK5)) = u1_struct_0(sK5) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1217,plain,
% 3.45/1.00      ( u1_struct_0(k8_tmap_1(sK5,sK5)) = u1_struct_0(sK5) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1215,c_35,c_34,c_33,c_45,c_51]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1940,plain,
% 3.45/1.00      ( u1_struct_0(k8_tmap_1(sK5,sK5)) = u1_struct_0(sK5) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_1217]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_834,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X2)
% 3.45/1.00      | X2 != X1
% 3.45/1.00      | X2 != X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_27]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_835,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.45/1.00      | ~ l1_pre_topc(X0) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_834]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1956,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.45/1.00      | ~ l1_pre_topc(X0_53) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_835]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2755,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X0_53))) = iProver_top
% 3.45/1.00      | l1_pre_topc(X0_53) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1956]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7165,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.45/1.00      | l1_pre_topc(k8_tmap_1(sK5,sK5)) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1940,c_2755]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_44,plain,
% 3.45/1.00      ( m1_pre_topc(X0,X0) = iProver_top
% 3.45/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_46,plain,
% 3.45/1.00      ( m1_pre_topc(sK5,sK5) = iProver_top
% 3.45/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_44]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_47,plain,
% 3.45/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.45/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.45/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_49,plain,
% 3.45/1.00      ( m1_pre_topc(sK5,sK5) != iProver_top
% 3.45/1.00      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.45/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_47]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7328,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_7165,c_38,c_46,c_49]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7333,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(sK5)
% 3.45/1.00      | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_7328,c_2772]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_816,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X2)
% 3.45/1.00      | X2 != X1
% 3.45/1.00      | X2 != X0
% 3.45/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_215,c_27]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_817,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | ~ v2_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0)
% 3.45/1.00      | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X0,X0)) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_816]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1222,plain,
% 3.45/1.00      ( ~ v2_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0)
% 3.45/1.00      | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X0,X0))
% 3.45/1.00      | sK5 != X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_817,c_35]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1223,plain,
% 3.45/1.00      ( ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(k8_tmap_1(sK5,sK5)) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1222]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_48,plain,
% 3.45/1.00      ( ~ m1_pre_topc(sK5,sK5)
% 3.45/1.00      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.45/1.00      | ~ l1_pre_topc(sK5) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_54,plain,
% 3.45/1.00      ( ~ m1_pre_topc(sK5,sK5)
% 3.45/1.00      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.45/1.00      | v2_struct_0(sK5)
% 3.45/1.00      | ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(k8_tmap_1(sK5,sK5)) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1225,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(k8_tmap_1(sK5,sK5)) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1223,c_35,c_34,c_33,c_45,c_48,c_54]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1939,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(k8_tmap_1(sK5,sK5)) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_1225]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7344,plain,
% 3.45/1.00      ( u1_pre_topc(k8_tmap_1(sK5,sK5)) = u1_pre_topc(sK5)
% 3.45/1.00      | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_7333,c_1939]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_37,plain,
% 3.45/1.00      ( v2_pre_topc(sK5) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_12,plain,
% 3.45/1.00      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 3.45/1.00      | ~ v2_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_89,plain,
% 3.45/1.00      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 3.45/1.00      | v2_pre_topc(X0) != iProver_top
% 3.45/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_91,plain,
% 3.45/1.00      ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top
% 3.45/1.00      | v2_pre_topc(sK5) != iProver_top
% 3.45/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_89]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7167,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,u1_struct_0(sK5)) = u1_pre_topc(sK5)
% 3.45/1.00      | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
% 3.45/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_2755,c_2772]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7194,plain,
% 3.45/1.00      ( u1_pre_topc(k8_tmap_1(sK5,sK5)) = u1_pre_topc(sK5)
% 3.45/1.00      | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
% 3.45/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_7167,c_1939]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7350,plain,
% 3.45/1.00      ( u1_pre_topc(k8_tmap_1(sK5,sK5)) = u1_pre_topc(sK5) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_7344,c_37,c_38,c_91,c_7194]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_0,plain,
% 3.45/1.00      ( ~ l1_pre_topc(X0)
% 3.45/1.00      | ~ v1_pre_topc(X0)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_21,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | v1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_864,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | ~ v2_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | v1_pre_topc(k8_tmap_1(X0,X2))
% 3.45/1.00      | X1 != X0
% 3.45/1.00      | X1 != X2 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_865,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | ~ v2_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0)
% 3.45/1.00      | v1_pre_topc(k8_tmap_1(X0,X0)) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_864]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1203,plain,
% 3.45/1.00      ( ~ v2_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0)
% 3.45/1.00      | v1_pre_topc(k8_tmap_1(X0,X0))
% 3.45/1.00      | sK5 != X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_865,c_35]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1204,plain,
% 3.45/1.00      ( ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | v1_pre_topc(k8_tmap_1(sK5,sK5)) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1203]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_63,plain,
% 3.45/1.00      ( ~ m1_pre_topc(sK5,sK5)
% 3.45/1.00      | v2_struct_0(sK5)
% 3.45/1.00      | ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | v1_pre_topc(k8_tmap_1(sK5,sK5)) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1206,plain,
% 3.45/1.00      ( v1_pre_topc(k8_tmap_1(sK5,sK5)) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1204,c_35,c_34,c_33,c_45,c_63]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1362,plain,
% 3.45/1.00      ( ~ l1_pre_topc(X0)
% 3.45/1.00      | k8_tmap_1(sK5,sK5) != X0
% 3.45/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_1206]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1363,plain,
% 3.45/1.00      ( ~ l1_pre_topc(k8_tmap_1(sK5,sK5))
% 3.45/1.00      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK5)),u1_pre_topc(k8_tmap_1(sK5,sK5))) = k8_tmap_1(sK5,sK5) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1362]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_19,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_69,plain,
% 3.45/1.00      ( ~ m1_pre_topc(sK5,sK5)
% 3.45/1.00      | v2_struct_0(sK5)
% 3.45/1.00      | ~ v2_pre_topc(sK5)
% 3.45/1.00      | l1_pre_topc(k8_tmap_1(sK5,sK5))
% 3.45/1.00      | ~ l1_pre_topc(sK5) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_483,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X2)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | k8_tmap_1(X1,X0) != X2
% 3.45/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X2 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_484,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 3.45/1.00      | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0))) = k8_tmap_1(X1,X0) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_483]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_486,plain,
% 3.45/1.00      ( ~ m1_pre_topc(sK5,sK5)
% 3.45/1.00      | v2_struct_0(sK5)
% 3.45/1.00      | ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(k8_tmap_1(sK5,sK5))
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK5)),u1_pre_topc(k8_tmap_1(sK5,sK5))) = k8_tmap_1(sK5,sK5) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_484]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1365,plain,
% 3.45/1.00      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK5)),u1_pre_topc(k8_tmap_1(sK5,sK5))) = k8_tmap_1(sK5,sK5) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1363,c_35,c_34,c_33,c_45,c_69,c_486]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1934,plain,
% 3.45/1.00      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK5)),u1_pre_topc(k8_tmap_1(sK5,sK5))) = k8_tmap_1(sK5,sK5) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_1365]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2820,plain,
% 3.45/1.00      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(k8_tmap_1(sK5,sK5))) = k8_tmap_1(sK5,sK5) ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_1934,c_1940]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7360,plain,
% 3.45/1.00      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK5) ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_7350,c_2820]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8810,plain,
% 3.45/1.00      ( u1_pre_topc(k8_tmap_1(sK5,sK6)) = u1_pre_topc(sK5)
% 3.45/1.00      | k8_tmap_1(sK5,sK5) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_6115,c_7360]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_987,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | ~ v2_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0)
% 3.45/1.00      | v1_pre_topc(k8_tmap_1(X0,X1))
% 3.45/1.00      | sK6 != X1
% 3.45/1.00      | sK5 != X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_201]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_988,plain,
% 3.45/1.00      ( v2_struct_0(sK5)
% 3.45/1.00      | ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | v1_pre_topc(k8_tmap_1(sK5,sK6)) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_987]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_990,plain,
% 3.45/1.00      ( v1_pre_topc(k8_tmap_1(sK5,sK6)) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_988,c_35,c_34,c_33]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1370,plain,
% 3.45/1.00      ( ~ l1_pre_topc(X0)
% 3.45/1.00      | k8_tmap_1(sK5,sK6) != X0
% 3.45/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_990]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1371,plain,
% 3.45/1.00      ( ~ l1_pre_topc(k8_tmap_1(sK5,sK6))
% 3.45/1.00      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK6)),u1_pre_topc(k8_tmap_1(sK5,sK6))) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1370]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1009,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | ~ v2_pre_topc(X0)
% 3.45/1.00      | ~ l1_pre_topc(X0)
% 3.45/1.00      | l1_pre_topc(k8_tmap_1(X0,X1))
% 3.45/1.00      | sK6 != X1
% 3.45/1.00      | sK5 != X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_201]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1010,plain,
% 3.45/1.00      ( v2_struct_0(sK5)
% 3.45/1.00      | ~ v2_pre_topc(sK5)
% 3.45/1.00      | l1_pre_topc(k8_tmap_1(sK5,sK6))
% 3.45/1.00      | ~ l1_pre_topc(sK5) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1009]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1103,plain,
% 3.45/1.00      ( ~ l1_pre_topc(X0)
% 3.45/1.00      | k8_tmap_1(sK5,sK6) != X0
% 3.45/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_990]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1104,plain,
% 3.45/1.00      ( ~ l1_pre_topc(k8_tmap_1(sK5,sK6))
% 3.45/1.00      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK6)),u1_pre_topc(k8_tmap_1(sK5,sK6))) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1103]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1373,plain,
% 3.45/1.00      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK6)),u1_pre_topc(k8_tmap_1(sK5,sK6))) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1371,c_35,c_34,c_33,c_1010,c_1104]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1947,plain,
% 3.45/1.00      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK5,sK6)),u1_pre_topc(k8_tmap_1(sK5,sK6))) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_1373]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_979,plain,
% 3.45/1.00      ( v2_struct_0(X0)
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1)
% 3.45/1.00      | sK6 != X0
% 3.45/1.00      | sK5 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_201]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_980,plain,
% 3.45/1.00      ( v2_struct_0(sK6)
% 3.45/1.00      | v2_struct_0(sK5)
% 3.45/1.00      | ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | u1_struct_0(k8_tmap_1(sK5,sK6)) = u1_struct_0(sK5) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_979]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_982,plain,
% 3.45/1.00      ( u1_struct_0(k8_tmap_1(sK5,sK6)) = u1_struct_0(sK5) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_980,c_35,c_34,c_33,c_32]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1950,plain,
% 3.45/1.00      ( u1_struct_0(k8_tmap_1(sK5,sK6)) = u1_struct_0(sK5) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_982]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2817,plain,
% 3.45/1.00      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(k8_tmap_1(sK5,sK6))) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_1947,c_1950]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8819,plain,
% 3.45/1.00      ( k8_tmap_1(sK5,sK5) = k8_tmap_1(sK5,sK6)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_8810,c_2817]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8882,plain,
% 3.45/1.00      ( k8_tmap_1(sK5,sK5) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_8819,c_7360]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8904,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(k8_tmap_1(sK5,sK5)) ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_8882,c_1952]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8907,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,u1_struct_0(sK6)) = u1_pre_topc(sK5) ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_8904,c_7350]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_16,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v1_tsep_1(X0,X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | sK4(X1,X0) = u1_struct_0(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_657,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | sK4(X1,X0) = u1_struct_0(X0) ),
% 3.45/1.00      inference(resolution,[status(thm)],[c_16,c_227]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_932,plain,
% 3.45/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | sK4(X1,X0) = u1_struct_0(X0)
% 3.45/1.00      | sK6 != X0
% 3.45/1.00      | sK5 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_657,c_201]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_933,plain,
% 3.45/1.00      ( v3_pre_topc(u1_struct_0(sK6),sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | sK4(sK5,sK6) = u1_struct_0(sK6) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_932]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_935,plain,
% 3.45/1.00      ( v3_pre_topc(u1_struct_0(sK6),sK5)
% 3.45/1.00      | sK4(sK5,sK6) = u1_struct_0(sK6) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_933,c_33]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1954,plain,
% 3.45/1.00      ( v3_pre_topc(u1_struct_0(sK6),sK5)
% 3.45/1.00      | sK4(sK5,sK6) = u1_struct_0(sK6) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_935]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2757,plain,
% 3.45/1.00      ( sK4(sK5,sK6) = u1_struct_0(sK6)
% 3.45/1.00      | v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1954]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5919,plain,
% 3.45/1.00      ( u1_pre_topc(k8_tmap_1(sK5,sK6)) = u1_pre_topc(sK5)
% 3.45/1.00      | sK4(sK5,sK6) = u1_struct_0(sK6) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_2757,c_5787]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_22,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 3.45/1.00      | v2_struct_0(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1293,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
% 3.45/1.00      | sK5 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_35]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1294,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.45/1.00      | r2_hidden(X0,u1_pre_topc(sK5))
% 3.45/1.00      | ~ v2_pre_topc(sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | k5_tmap_1(sK5,X0) != u1_pre_topc(sK5) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_1293]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1298,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.45/1.00      | r2_hidden(X0,u1_pre_topc(sK5))
% 3.45/1.00      | k5_tmap_1(sK5,X0) != u1_pre_topc(sK5) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1294,c_34,c_33]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1935,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.45/1.00      | r2_hidden(X0_54,u1_pre_topc(sK5))
% 3.45/1.00      | k5_tmap_1(sK5,X0_54) != u1_pre_topc(sK5) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_1298]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2773,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,X0_54) != u1_pre_topc(sK5)
% 3.45/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.45/1.00      | r2_hidden(X0_54,u1_pre_topc(sK5)) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1935]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4087,plain,
% 3.45/1.00      ( u1_pre_topc(k8_tmap_1(sK5,sK6)) != u1_pre_topc(sK5)
% 3.45/1.00      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.45/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1952,c_2773]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_970,plain,
% 3.45/1.00      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.45/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_969]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4690,plain,
% 3.45/1.00      ( u1_pre_topc(k8_tmap_1(sK5,sK6)) != u1_pre_topc(sK5)
% 3.45/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_4087,c_38,c_970]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6896,plain,
% 3.45/1.00      ( sK4(sK5,sK6) = u1_struct_0(sK6)
% 3.45/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5919,c_4690]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_28,negated_conjecture,
% 3.45/1.00      ( ~ m1_pre_topc(sK6,sK5)
% 3.45/1.00      | ~ v1_tsep_1(sK6,sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_293,plain,
% 3.45/1.00      ( ~ v1_tsep_1(sK6,sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(prop_impl,[status(thm)],[c_31,c_28]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_706,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | sK4(X1,X0) = u1_struct_0(X0)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6)
% 3.45/1.00      | sK6 != X0
% 3.45/1.00      | sK5 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_293]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_707,plain,
% 3.45/1.00      ( ~ m1_pre_topc(sK6,sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | sK4(sK5,sK6) = u1_struct_0(sK6)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_706]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_709,plain,
% 3.45/1.00      ( sK4(sK5,sK6) = u1_struct_0(sK6)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_707,c_33,c_31]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1962,plain,
% 3.45/1.00      ( sK4(sK5,sK6) = u1_struct_0(sK6)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_709]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6898,plain,
% 3.45/1.00      ( sK4(sK5,sK6) = u1_struct_0(sK6)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5919,c_2817]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6998,plain,
% 3.45/1.00      ( sK4(sK5,sK6) = u1_struct_0(sK6) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_6896,c_1962,c_6898]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_15,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | v1_tsep_1(X0,X1)
% 3.45/1.00      | ~ v3_pre_topc(sK4(X1,X0),X1)
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_717,plain,
% 3.45/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.00      | ~ v3_pre_topc(sK4(X1,X0),X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6)
% 3.45/1.00      | sK6 != X0
% 3.45/1.00      | sK5 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_293]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_718,plain,
% 3.45/1.00      ( ~ m1_pre_topc(sK6,sK5)
% 3.45/1.00      | ~ v3_pre_topc(sK4(sK5,sK6),sK5)
% 3.45/1.00      | ~ l1_pre_topc(sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_717]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_720,plain,
% 3.45/1.00      ( ~ v3_pre_topc(sK4(sK5,sK6),sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_718,c_33,c_31]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1961,plain,
% 3.45/1.00      ( ~ v3_pre_topc(sK4(sK5,sK6),sK5)
% 3.45/1.00      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_720]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2750,plain,
% 3.45/1.00      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6)
% 3.45/1.00      | v3_pre_topc(sK4(sK5,sK6),sK5) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1961]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7002,plain,
% 3.45/1.00      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k8_tmap_1(sK5,sK6)
% 3.45/1.00      | v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_6998,c_2750]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8720,plain,
% 3.45/1.00      ( k8_tmap_1(sK5,sK5) != k8_tmap_1(sK5,sK6)
% 3.45/1.00      | v3_pre_topc(u1_struct_0(sK6),sK5) != iProver_top ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_7002,c_7360]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_13,plain,
% 3.45/1.00      ( v3_pre_topc(X0,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1967,plain,
% 3.45/1.00      ( v3_pre_topc(X0_54,X0_53)
% 3.45/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_53)))
% 3.45/1.00      | ~ r2_hidden(X0_54,u1_pre_topc(X0_53))
% 3.45/1.00      | ~ l1_pre_topc(X0_53) ),
% 3.45/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3243,plain,
% 3.45/1.00      ( v3_pre_topc(u1_struct_0(sK6),sK5)
% 3.45/1.00      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.45/1.00      | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5))
% 3.45/1.00      | ~ l1_pre_topc(sK5) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1967]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3244,plain,
% 3.45/1.00      ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top
% 3.45/1.00      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.45/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) != iProver_top
% 3.45/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_3243]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3119,plain,
% 3.45/1.00      ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.45/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5))
% 3.45/1.00      | k5_tmap_1(sK5,u1_struct_0(sK6)) != u1_pre_topc(sK5) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1935]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3120,plain,
% 3.45/1.00      ( k5_tmap_1(sK5,u1_struct_0(sK6)) != u1_pre_topc(sK5)
% 3.45/1.00      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.45/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_3119]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(contradiction,plain,
% 3.45/1.00      ( $false ),
% 3.45/1.00      inference(minisat,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_8907,c_8882,c_8720,c_3244,c_3120,c_970,c_38]) ).
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  ------                               Statistics
% 3.45/1.00  
% 3.45/1.00  ------ General
% 3.45/1.00  
% 3.45/1.00  abstr_ref_over_cycles:                  0
% 3.45/1.00  abstr_ref_under_cycles:                 0
% 3.45/1.00  gc_basic_clause_elim:                   0
% 3.45/1.00  forced_gc_time:                         0
% 3.45/1.00  parsing_time:                           0.009
% 3.45/1.00  unif_index_cands_time:                  0.
% 3.45/1.00  unif_index_add_time:                    0.
% 3.45/1.00  orderings_time:                         0.
% 3.45/1.00  out_proof_time:                         0.02
% 3.45/1.00  total_time:                             0.336
% 3.45/1.00  num_of_symbols:                         64
% 3.45/1.00  num_of_terms:                           5106
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing
% 3.45/1.00  
% 3.45/1.00  num_of_splits:                          2
% 3.45/1.00  num_of_split_atoms:                     2
% 3.45/1.00  num_of_reused_defs:                     0
% 3.45/1.00  num_eq_ax_congr_red:                    12
% 3.45/1.00  num_of_sem_filtered_clauses:            1
% 3.45/1.00  num_of_subtypes:                        3
% 3.45/1.00  monotx_restored_types:                  0
% 3.45/1.00  sat_num_of_epr_types:                   0
% 3.45/1.00  sat_num_of_non_cyclic_types:            0
% 3.45/1.00  sat_guarded_non_collapsed_types:        0
% 3.45/1.00  num_pure_diseq_elim:                    0
% 3.45/1.00  simp_replaced_by:                       0
% 3.45/1.00  res_preprocessed:                       176
% 3.45/1.00  prep_upred:                             0
% 3.45/1.00  prep_unflattend:                        76
% 3.45/1.00  smt_new_axioms:                         0
% 3.45/1.00  pred_elim_cands:                        11
% 3.45/1.00  pred_elim:                              4
% 3.45/1.00  pred_elim_cl:                           -12
% 3.45/1.00  pred_elim_cycles:                       9
% 3.45/1.00  merged_defs:                            2
% 3.45/1.00  merged_defs_ncl:                        0
% 3.45/1.00  bin_hyper_res:                          2
% 3.45/1.00  prep_cycles:                            3
% 3.45/1.00  pred_elim_time:                         0.029
% 3.45/1.00  splitting_time:                         0.
% 3.45/1.00  sem_filter_time:                        0.
% 3.45/1.00  monotx_time:                            0.
% 3.45/1.00  subtype_inf_time:                       0.
% 3.45/1.00  
% 3.45/1.00  ------ Problem properties
% 3.45/1.00  
% 3.45/1.00  clauses:                                49
% 3.45/1.00  conjectures:                            2
% 3.45/1.00  epr:                                    5
% 3.45/1.00  horn:                                   38
% 3.45/1.00  ground:                                 27
% 3.45/1.00  unary:                                  13
% 3.45/1.00  binary:                                 13
% 3.45/1.00  lits:                                   123
% 3.45/1.00  lits_eq:                                20
% 3.45/1.00  fd_pure:                                0
% 3.45/1.00  fd_pseudo:                              0
% 3.45/1.00  fd_cond:                                0
% 3.45/1.00  fd_pseudo_cond:                         0
% 3.45/1.00  ac_symbols:                             0
% 3.45/1.00  
% 3.45/1.00  ------ Propositional Solver
% 3.45/1.00  
% 3.45/1.00  prop_solver_calls:                      23
% 3.45/1.00  prop_fast_solver_calls:                 1764
% 3.45/1.00  smt_solver_calls:                       0
% 3.45/1.00  smt_fast_solver_calls:                  0
% 3.45/1.00  prop_num_of_clauses:                    2650
% 3.45/1.00  prop_preprocess_simplified:             8170
% 3.45/1.00  prop_fo_subsumed:                       100
% 3.45/1.00  prop_solver_time:                       0.
% 3.45/1.00  smt_solver_time:                        0.
% 3.45/1.00  smt_fast_solver_time:                   0.
% 3.45/1.00  prop_fast_solver_time:                  0.
% 3.45/1.00  prop_unsat_core_time:                   0.
% 3.45/1.00  
% 3.45/1.00  ------ QBF
% 3.45/1.00  
% 3.45/1.00  qbf_q_res:                              0
% 3.45/1.00  qbf_num_tautologies:                    0
% 3.45/1.00  qbf_prep_cycles:                        0
% 3.45/1.00  
% 3.45/1.00  ------ BMC1
% 3.45/1.00  
% 3.45/1.00  bmc1_current_bound:                     -1
% 3.45/1.00  bmc1_last_solved_bound:                 -1
% 3.45/1.00  bmc1_unsat_core_size:                   -1
% 3.45/1.00  bmc1_unsat_core_parents_size:           -1
% 3.45/1.00  bmc1_merge_next_fun:                    0
% 3.45/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation
% 3.45/1.00  
% 3.45/1.00  inst_num_of_clauses:                    863
% 3.45/1.00  inst_num_in_passive:                    114
% 3.45/1.00  inst_num_in_active:                     476
% 3.45/1.00  inst_num_in_unprocessed:                273
% 3.45/1.00  inst_num_of_loops:                      530
% 3.45/1.00  inst_num_of_learning_restarts:          0
% 3.45/1.00  inst_num_moves_active_passive:          50
% 3.45/1.00  inst_lit_activity:                      0
% 3.45/1.00  inst_lit_activity_moves:                0
% 3.45/1.00  inst_num_tautologies:                   0
% 3.45/1.00  inst_num_prop_implied:                  0
% 3.45/1.00  inst_num_existing_simplified:           0
% 3.45/1.00  inst_num_eq_res_simplified:             0
% 3.45/1.00  inst_num_child_elim:                    0
% 3.45/1.00  inst_num_of_dismatching_blockings:      587
% 3.45/1.00  inst_num_of_non_proper_insts:           885
% 3.45/1.00  inst_num_of_duplicates:                 0
% 3.45/1.00  inst_inst_num_from_inst_to_res:         0
% 3.45/1.00  inst_dismatching_checking_time:         0.
% 3.45/1.00  
% 3.45/1.00  ------ Resolution
% 3.45/1.00  
% 3.45/1.00  res_num_of_clauses:                     0
% 3.45/1.00  res_num_in_passive:                     0
% 3.45/1.00  res_num_in_active:                      0
% 3.45/1.00  res_num_of_loops:                       179
% 3.45/1.00  res_forward_subset_subsumed:            43
% 3.45/1.00  res_backward_subset_subsumed:           2
% 3.45/1.00  res_forward_subsumed:                   0
% 3.45/1.00  res_backward_subsumed:                  0
% 3.45/1.00  res_forward_subsumption_resolution:     0
% 3.45/1.00  res_backward_subsumption_resolution:    0
% 3.45/1.00  res_clause_to_clause_subsumption:       295
% 3.45/1.00  res_orphan_elimination:                 0
% 3.45/1.00  res_tautology_del:                      94
% 3.45/1.00  res_num_eq_res_simplified:              0
% 3.45/1.00  res_num_sel_changes:                    0
% 3.45/1.00  res_moves_from_active_to_pass:          0
% 3.45/1.00  
% 3.45/1.00  ------ Superposition
% 3.45/1.00  
% 3.45/1.00  sup_time_total:                         0.
% 3.45/1.00  sup_time_generating:                    0.
% 3.45/1.00  sup_time_sim_full:                      0.
% 3.45/1.00  sup_time_sim_immed:                     0.
% 3.45/1.00  
% 3.45/1.00  sup_num_of_clauses:                     73
% 3.45/1.00  sup_num_in_active:                      69
% 3.45/1.00  sup_num_in_passive:                     4
% 3.45/1.00  sup_num_of_loops:                       105
% 3.45/1.00  sup_fw_superposition:                   93
% 3.45/1.00  sup_bw_superposition:                   84
% 3.45/1.00  sup_immediate_simplified:               120
% 3.45/1.00  sup_given_eliminated:                   1
% 3.45/1.00  comparisons_done:                       0
% 3.45/1.00  comparisons_avoided:                    6
% 3.45/1.00  
% 3.45/1.00  ------ Simplifications
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  sim_fw_subset_subsumed:                 94
% 3.45/1.00  sim_bw_subset_subsumed:                 18
% 3.45/1.00  sim_fw_subsumed:                        16
% 3.45/1.00  sim_bw_subsumed:                        1
% 3.45/1.00  sim_fw_subsumption_res:                 0
% 3.45/1.00  sim_bw_subsumption_res:                 0
% 3.45/1.00  sim_tautology_del:                      12
% 3.45/1.00  sim_eq_tautology_del:                   0
% 3.45/1.00  sim_eq_res_simp:                        2
% 3.45/1.00  sim_fw_demodulated:                     3
% 3.45/1.00  sim_bw_demodulated:                     33
% 3.45/1.00  sim_light_normalised:                   38
% 3.45/1.00  sim_joinable_taut:                      0
% 3.45/1.00  sim_joinable_simp:                      0
% 3.45/1.00  sim_ac_normalised:                      0
% 3.45/1.00  sim_smt_subsumption:                    0
% 3.45/1.00  
%------------------------------------------------------------------------------
