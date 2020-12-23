%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:02 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  243 (2055 expanded)
%              Number of clauses        :  157 ( 594 expanded)
%              Number of leaves         :   25 ( 444 expanded)
%              Depth                    :   26
%              Number of atoms          : 1019 (14399 expanded)
%              Number of equality atoms :  416 (3032 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f24,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f62])).

fof(f75,plain,(
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
    inference(flattening,[],[f74])).

fof(f77,plain,(
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
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK3)
          | ~ m1_pre_topc(sK3,X0)
          | ~ v1_tsep_1(sK3,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK3)
          | ( m1_pre_topc(sK3,X0)
            & v1_tsep_1(sK3,X0) ) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
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
          ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,X1)
            | ~ m1_pre_topc(X1,sK2)
            | ~ v1_tsep_1(X1,sK2) )
          & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,X1)
            | ( m1_pre_topc(X1,sK2)
              & v1_tsep_1(X1,sK2) ) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
      | ~ m1_pre_topc(sK3,sK2)
      | ~ v1_tsep_1(sK3,sK2) )
    & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
      | ( m1_pre_topc(sK3,sK2)
        & v1_tsep_1(sK3,sK2) ) )
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f75,f77,f76])).

fof(f123,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f120,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f121,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f90,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f86,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f91,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f115,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f73,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f109,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f119,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f70,plain,(
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
    inference(rectify,[],[f69])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0,X1),X0)
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f70,f71])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f126,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK1(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f13,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f66,plain,(
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
    inference(rectify,[],[f65])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f66,f67])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f127,plain,(
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
    inference(equality_resolution,[],[f97])).

fof(f128,plain,(
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
    inference(equality_resolution,[],[f127])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f108,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f105,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f112,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f129,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f124,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_8297,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = u1_pre_topc(X0)
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_9829,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | X2 = u1_pre_topc(X0)
    | g1_pre_topc(X3,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_8297])).

cnf(c_13954,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X0))
    | u1_pre_topc(X2) = u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_9829])).

cnf(c_35784,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(sK2))
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_13954])).

cnf(c_35797,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_35784])).

cnf(c_34,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_7576,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_43,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_7571,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_39,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_7572,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_10057,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7571,c_7572])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_49,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_50,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_10348,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10057,c_49,c_50])).

cnf(c_10356,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7576,c_10348])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_7593,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8099,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7571,c_7593])).

cnf(c_10368,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10356,c_50,c_8099])).

cnf(c_10369,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_10368])).

cnf(c_8978,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7576,c_7593])).

cnf(c_9003,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7571,c_8978])).

cnf(c_9382,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9003,c_50])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7596,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9387,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9382,c_7596])).

cnf(c_35,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_7575,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_8756,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7571,c_7575])).

cnf(c_9480,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9387,c_50,c_8756])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_7588,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9488,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9480,c_7588])).

cnf(c_9651,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9488])).

cnf(c_12,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_7592,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9487,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9480,c_7588])).

cnf(c_9532,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9487])).

cnf(c_9767,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7592,c_9532])).

cnf(c_10668,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9651,c_50,c_8099,c_9767])).

cnf(c_36,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_7574,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_10714,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10668,c_7574])).

cnf(c_14404,plain,
    ( m1_pre_topc(sK3,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10369,c_10714])).

cnf(c_52,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_8369,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_8370,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8369])).

cnf(c_14508,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14404,c_50,c_52,c_8370])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_7579,plain,
    ( k5_tmap_1(X0,X1) = u1_pre_topc(X0)
    | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_14517,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14508,c_7579])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_48,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_23,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_40,negated_conjecture,
    ( ~ v1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_384,plain,
    ( ~ v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_43,c_40])).

cnf(c_788,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_384])).

cnf(c_789,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_791,plain,
    ( sK1(sK2,sK3) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_789,c_45,c_43])).

cnf(c_22,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK1(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_799,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK1(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_384])).

cnf(c_800,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_802,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_800,c_45,c_43])).

cnf(c_804,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_6812,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_6828,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6812])).

cnf(c_6813,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_6829,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6813])).

cnf(c_6806,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6841,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_6806])).

cnf(c_8180,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_8184,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8180])).

cnf(c_8894,plain,
    ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6806])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_29,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_301,plain,
    ( ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_36,c_29,c_28,c_27])).

cnf(c_302,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_301])).

cnf(c_9302,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_6817,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8086,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X3)
    | X1 != X3
    | X0 != u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_6817])).

cnf(c_9715,plain,
    ( v3_pre_topc(sK1(sK2,sK3),X0)
    | ~ v3_pre_topc(u1_struct_0(sK3),X1)
    | X0 != X1
    | sK1(sK2,sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_8086])).

cnf(c_9716,plain,
    ( X0 != X1
    | sK1(sK2,sK3) != u1_struct_0(sK3)
    | v3_pre_topc(sK1(sK2,sK3),X0) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9715])).

cnf(c_9718,plain,
    ( sK1(sK2,sK3) != u1_struct_0(sK3)
    | sK2 != sK2
    | v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9716])).

cnf(c_6807,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_8408,plain,
    ( X0 != X1
    | u1_pre_topc(sK2) != X1
    | u1_pre_topc(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_6807])).

cnf(c_8851,plain,
    ( X0 != u1_pre_topc(sK2)
    | u1_pre_topc(sK2) = X0
    | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_8408])).

cnf(c_10091,plain,
    ( k5_tmap_1(sK2,u1_struct_0(X0)) != u1_pre_topc(sK2)
    | u1_pre_topc(sK2) = k5_tmap_1(sK2,u1_struct_0(X0))
    | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_8851])).

cnf(c_11277,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) != u1_pre_topc(sK2)
    | u1_pre_topc(sK2) = k5_tmap_1(sK2,u1_struct_0(sK3))
    | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_10091])).

cnf(c_8605,plain,
    ( X0 != X1
    | k8_tmap_1(X2,X3) != X1
    | k8_tmap_1(X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_6807])).

cnf(c_9192,plain,
    ( X0 != k8_tmap_1(X1,X2)
    | k8_tmap_1(X1,X2) = X0
    | k8_tmap_1(X1,X2) != k8_tmap_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_8605])).

cnf(c_10326,plain,
    ( k6_tmap_1(X0,u1_struct_0(X1)) != k8_tmap_1(X0,X1)
    | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
    | k8_tmap_1(X0,X1) != k8_tmap_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_9192])).

cnf(c_15666,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_10326])).

cnf(c_8,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_7595,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14515,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14508,c_7595])).

cnf(c_8181,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_8182,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8181])).

cnf(c_17300,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14515,c_50,c_52,c_8182,c_8370])).

cnf(c_17301,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_17300])).

cnf(c_8396,plain,
    ( k8_tmap_1(sK2,sK3) != X0
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(X1,X2)
    | g1_pre_topc(X1,X2) != X0 ),
    inference(instantiation,[status(thm)],[c_6807])).

cnf(c_15667,plain,
    ( k8_tmap_1(sK2,sK3) != k6_tmap_1(sK2,u1_struct_0(sK3))
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(X0,X1)
    | g1_pre_topc(X0,X1) != k6_tmap_1(sK2,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8396])).

cnf(c_18877,plain,
    ( k8_tmap_1(sK2,sK3) != k6_tmap_1(sK2,u1_struct_0(sK3))
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3)))
    | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3))) != k6_tmap_1(sK2,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_15667])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_8120,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,u1_struct_0(X0))) = k6_tmap_1(X1,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_18878,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3))) = k6_tmap_1(sK2,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8120])).

cnf(c_8033,plain,
    ( k8_tmap_1(sK2,sK3) != X0
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6807])).

cnf(c_8197,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(X0,X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1) ),
    inference(instantiation,[status(thm)],[c_8033])).

cnf(c_19956,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_8197])).

cnf(c_6814,plain,
    ( X0 != X1
    | X2 != X3
    | g1_pre_topc(X0,X2) = g1_pre_topc(X1,X3) ),
    theory(equality)).

cnf(c_8587,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(X1,X2)
    | u1_pre_topc(X0) != X2
    | u1_struct_0(X0) != X1 ),
    inference(instantiation,[status(thm)],[c_6814])).

cnf(c_13776,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(X0,k5_tmap_1(sK2,u1_struct_0(X1)))
    | u1_pre_topc(sK2) != k5_tmap_1(sK2,u1_struct_0(X1))
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_8587])).

cnf(c_18329,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(X0)))
    | u1_pre_topc(sK2) != k5_tmap_1(sK2,u1_struct_0(X0))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_13776])).

cnf(c_29050,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3)))
    | u1_pre_topc(sK2) != k5_tmap_1(sK2,u1_struct_0(sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_18329])).

cnf(c_29676,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14517,c_47,c_48,c_46,c_49,c_45,c_50,c_43,c_52,c_791,c_804,c_6828,c_6829,c_6841,c_8184,c_8369,c_8370,c_8894,c_9302,c_9718,c_11277,c_15666,c_17301,c_18877,c_18878,c_19956,c_29050])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_7578,plain,
    ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_14519,plain,
    ( u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK3))) = k5_tmap_1(sK2,u1_struct_0(sK3))
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14508,c_7578])).

cnf(c_7566,plain,
    ( k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_11940,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3)
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7571,c_7566])).

cnf(c_12409,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11940,c_47,c_46,c_45,c_43,c_9302])).

cnf(c_14534,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3))
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14519,c_12409])).

cnf(c_15041,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14534,c_48,c_49,c_50])).

cnf(c_30,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_7580,plain,
    ( k5_tmap_1(X0,X1) != u1_pre_topc(X0)
    | r2_hidden(X1,u1_pre_topc(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_15044,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15041,c_7580])).

cnf(c_20714,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15044,c_48,c_49,c_50,c_52,c_8370])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_7594,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14516,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14508,c_7594])).

cnf(c_8035,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8036,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8035])).

cnf(c_17307,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14516,c_50,c_52,c_8036,c_8370])).

cnf(c_17308,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_17307])).

cnf(c_12642,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_10652,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_8579,plain,
    ( X0 != X1
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X0 ),
    inference(instantiation,[status(thm)],[c_6807])).

cnf(c_9165,plain,
    ( X0 != k8_tmap_1(X1,X2)
    | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X2)),u1_pre_topc(k8_tmap_1(X1,X2))) = X0
    | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X2)),u1_pre_topc(k8_tmap_1(X1,X2))) != k8_tmap_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_8579])).

cnf(c_10481,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_9165])).

cnf(c_8038,plain,
    ( ~ l1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v1_pre_topc(k8_tmap_1(X0,X1))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9312,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v1_pre_topc(k8_tmap_1(sK2,sK3))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_8038])).

cnf(c_25,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_291,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_36])).

cnf(c_292,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_291])).

cnf(c_42,negated_conjecture,
    ( v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_386,plain,
    ( v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_42])).

cnf(c_813,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_292,c_386])).

cnf(c_814,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v3_pre_topc(u1_struct_0(sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_816,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_814,c_45,c_43])).

cnf(c_818,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_134,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35797,c_29676,c_20714,c_17308,c_12642,c_10652,c_10481,c_9312,c_818,c_134,c_43,c_45,c_46,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.94/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/1.51  
% 7.94/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.94/1.51  
% 7.94/1.51  ------  iProver source info
% 7.94/1.51  
% 7.94/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.94/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.94/1.51  git: non_committed_changes: false
% 7.94/1.51  git: last_make_outside_of_git: false
% 7.94/1.51  
% 7.94/1.51  ------ 
% 7.94/1.51  
% 7.94/1.51  ------ Input Options
% 7.94/1.51  
% 7.94/1.51  --out_options                           all
% 7.94/1.51  --tptp_safe_out                         true
% 7.94/1.51  --problem_path                          ""
% 7.94/1.51  --include_path                          ""
% 7.94/1.51  --clausifier                            res/vclausify_rel
% 7.94/1.51  --clausifier_options                    --mode clausify
% 7.94/1.51  --stdin                                 false
% 7.94/1.51  --stats_out                             all
% 7.94/1.51  
% 7.94/1.51  ------ General Options
% 7.94/1.51  
% 7.94/1.51  --fof                                   false
% 7.94/1.51  --time_out_real                         305.
% 7.94/1.51  --time_out_virtual                      -1.
% 7.94/1.51  --symbol_type_check                     false
% 7.94/1.51  --clausify_out                          false
% 7.94/1.51  --sig_cnt_out                           false
% 7.94/1.51  --trig_cnt_out                          false
% 7.94/1.51  --trig_cnt_out_tolerance                1.
% 7.94/1.51  --trig_cnt_out_sk_spl                   false
% 7.94/1.51  --abstr_cl_out                          false
% 7.94/1.51  
% 7.94/1.51  ------ Global Options
% 7.94/1.51  
% 7.94/1.51  --schedule                              default
% 7.94/1.51  --add_important_lit                     false
% 7.94/1.51  --prop_solver_per_cl                    1000
% 7.94/1.51  --min_unsat_core                        false
% 7.94/1.51  --soft_assumptions                      false
% 7.94/1.51  --soft_lemma_size                       3
% 7.94/1.51  --prop_impl_unit_size                   0
% 7.94/1.51  --prop_impl_unit                        []
% 7.94/1.51  --share_sel_clauses                     true
% 7.94/1.51  --reset_solvers                         false
% 7.94/1.51  --bc_imp_inh                            [conj_cone]
% 7.94/1.51  --conj_cone_tolerance                   3.
% 7.94/1.51  --extra_neg_conj                        none
% 7.94/1.51  --large_theory_mode                     true
% 7.94/1.51  --prolific_symb_bound                   200
% 7.94/1.51  --lt_threshold                          2000
% 7.94/1.51  --clause_weak_htbl                      true
% 7.94/1.51  --gc_record_bc_elim                     false
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing Options
% 7.94/1.51  
% 7.94/1.51  --preprocessing_flag                    true
% 7.94/1.51  --time_out_prep_mult                    0.1
% 7.94/1.51  --splitting_mode                        input
% 7.94/1.51  --splitting_grd                         true
% 7.94/1.51  --splitting_cvd                         false
% 7.94/1.51  --splitting_cvd_svl                     false
% 7.94/1.51  --splitting_nvd                         32
% 7.94/1.51  --sub_typing                            true
% 7.94/1.51  --prep_gs_sim                           true
% 7.94/1.51  --prep_unflatten                        true
% 7.94/1.51  --prep_res_sim                          true
% 7.94/1.51  --prep_upred                            true
% 7.94/1.51  --prep_sem_filter                       exhaustive
% 7.94/1.51  --prep_sem_filter_out                   false
% 7.94/1.51  --pred_elim                             true
% 7.94/1.51  --res_sim_input                         true
% 7.94/1.51  --eq_ax_congr_red                       true
% 7.94/1.51  --pure_diseq_elim                       true
% 7.94/1.51  --brand_transform                       false
% 7.94/1.51  --non_eq_to_eq                          false
% 7.94/1.51  --prep_def_merge                        true
% 7.94/1.51  --prep_def_merge_prop_impl              false
% 7.94/1.51  --prep_def_merge_mbd                    true
% 7.94/1.51  --prep_def_merge_tr_red                 false
% 7.94/1.51  --prep_def_merge_tr_cl                  false
% 7.94/1.51  --smt_preprocessing                     true
% 7.94/1.51  --smt_ac_axioms                         fast
% 7.94/1.51  --preprocessed_out                      false
% 7.94/1.51  --preprocessed_stats                    false
% 7.94/1.51  
% 7.94/1.51  ------ Abstraction refinement Options
% 7.94/1.51  
% 7.94/1.51  --abstr_ref                             []
% 7.94/1.51  --abstr_ref_prep                        false
% 7.94/1.51  --abstr_ref_until_sat                   false
% 7.94/1.51  --abstr_ref_sig_restrict                funpre
% 7.94/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.94/1.51  --abstr_ref_under                       []
% 7.94/1.51  
% 7.94/1.51  ------ SAT Options
% 7.94/1.51  
% 7.94/1.51  --sat_mode                              false
% 7.94/1.51  --sat_fm_restart_options                ""
% 7.94/1.51  --sat_gr_def                            false
% 7.94/1.51  --sat_epr_types                         true
% 7.94/1.51  --sat_non_cyclic_types                  false
% 7.94/1.51  --sat_finite_models                     false
% 7.94/1.51  --sat_fm_lemmas                         false
% 7.94/1.51  --sat_fm_prep                           false
% 7.94/1.51  --sat_fm_uc_incr                        true
% 7.94/1.51  --sat_out_model                         small
% 7.94/1.51  --sat_out_clauses                       false
% 7.94/1.51  
% 7.94/1.51  ------ QBF Options
% 7.94/1.51  
% 7.94/1.51  --qbf_mode                              false
% 7.94/1.51  --qbf_elim_univ                         false
% 7.94/1.51  --qbf_dom_inst                          none
% 7.94/1.51  --qbf_dom_pre_inst                      false
% 7.94/1.51  --qbf_sk_in                             false
% 7.94/1.51  --qbf_pred_elim                         true
% 7.94/1.51  --qbf_split                             512
% 7.94/1.51  
% 7.94/1.51  ------ BMC1 Options
% 7.94/1.51  
% 7.94/1.51  --bmc1_incremental                      false
% 7.94/1.51  --bmc1_axioms                           reachable_all
% 7.94/1.51  --bmc1_min_bound                        0
% 7.94/1.51  --bmc1_max_bound                        -1
% 7.94/1.51  --bmc1_max_bound_default                -1
% 7.94/1.51  --bmc1_symbol_reachability              true
% 7.94/1.51  --bmc1_property_lemmas                  false
% 7.94/1.51  --bmc1_k_induction                      false
% 7.94/1.51  --bmc1_non_equiv_states                 false
% 7.94/1.51  --bmc1_deadlock                         false
% 7.94/1.51  --bmc1_ucm                              false
% 7.94/1.51  --bmc1_add_unsat_core                   none
% 7.94/1.51  --bmc1_unsat_core_children              false
% 7.94/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.94/1.51  --bmc1_out_stat                         full
% 7.94/1.51  --bmc1_ground_init                      false
% 7.94/1.51  --bmc1_pre_inst_next_state              false
% 7.94/1.51  --bmc1_pre_inst_state                   false
% 7.94/1.51  --bmc1_pre_inst_reach_state             false
% 7.94/1.51  --bmc1_out_unsat_core                   false
% 7.94/1.51  --bmc1_aig_witness_out                  false
% 7.94/1.51  --bmc1_verbose                          false
% 7.94/1.51  --bmc1_dump_clauses_tptp                false
% 7.94/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.94/1.51  --bmc1_dump_file                        -
% 7.94/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.94/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.94/1.51  --bmc1_ucm_extend_mode                  1
% 7.94/1.51  --bmc1_ucm_init_mode                    2
% 7.94/1.51  --bmc1_ucm_cone_mode                    none
% 7.94/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.94/1.51  --bmc1_ucm_relax_model                  4
% 7.94/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.94/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.94/1.51  --bmc1_ucm_layered_model                none
% 7.94/1.51  --bmc1_ucm_max_lemma_size               10
% 7.94/1.51  
% 7.94/1.51  ------ AIG Options
% 7.94/1.51  
% 7.94/1.51  --aig_mode                              false
% 7.94/1.51  
% 7.94/1.51  ------ Instantiation Options
% 7.94/1.51  
% 7.94/1.51  --instantiation_flag                    true
% 7.94/1.51  --inst_sos_flag                         false
% 7.94/1.51  --inst_sos_phase                        true
% 7.94/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.94/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.94/1.51  --inst_lit_sel_side                     num_symb
% 7.94/1.51  --inst_solver_per_active                1400
% 7.94/1.51  --inst_solver_calls_frac                1.
% 7.94/1.51  --inst_passive_queue_type               priority_queues
% 7.94/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.94/1.51  --inst_passive_queues_freq              [25;2]
% 7.94/1.51  --inst_dismatching                      true
% 7.94/1.51  --inst_eager_unprocessed_to_passive     true
% 7.94/1.51  --inst_prop_sim_given                   true
% 7.94/1.51  --inst_prop_sim_new                     false
% 7.94/1.51  --inst_subs_new                         false
% 7.94/1.51  --inst_eq_res_simp                      false
% 7.94/1.51  --inst_subs_given                       false
% 7.94/1.51  --inst_orphan_elimination               true
% 7.94/1.51  --inst_learning_loop_flag               true
% 7.94/1.51  --inst_learning_start                   3000
% 7.94/1.51  --inst_learning_factor                  2
% 7.94/1.51  --inst_start_prop_sim_after_learn       3
% 7.94/1.51  --inst_sel_renew                        solver
% 7.94/1.51  --inst_lit_activity_flag                true
% 7.94/1.51  --inst_restr_to_given                   false
% 7.94/1.51  --inst_activity_threshold               500
% 7.94/1.51  --inst_out_proof                        true
% 7.94/1.51  
% 7.94/1.51  ------ Resolution Options
% 7.94/1.51  
% 7.94/1.51  --resolution_flag                       true
% 7.94/1.51  --res_lit_sel                           adaptive
% 7.94/1.51  --res_lit_sel_side                      none
% 7.94/1.51  --res_ordering                          kbo
% 7.94/1.51  --res_to_prop_solver                    active
% 7.94/1.51  --res_prop_simpl_new                    false
% 7.94/1.51  --res_prop_simpl_given                  true
% 7.94/1.51  --res_passive_queue_type                priority_queues
% 7.94/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.94/1.51  --res_passive_queues_freq               [15;5]
% 7.94/1.51  --res_forward_subs                      full
% 7.94/1.51  --res_backward_subs                     full
% 7.94/1.51  --res_forward_subs_resolution           true
% 7.94/1.51  --res_backward_subs_resolution          true
% 7.94/1.51  --res_orphan_elimination                true
% 7.94/1.51  --res_time_limit                        2.
% 7.94/1.51  --res_out_proof                         true
% 7.94/1.51  
% 7.94/1.51  ------ Superposition Options
% 7.94/1.51  
% 7.94/1.51  --superposition_flag                    true
% 7.94/1.51  --sup_passive_queue_type                priority_queues
% 7.94/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.94/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.94/1.51  --demod_completeness_check              fast
% 7.94/1.51  --demod_use_ground                      true
% 7.94/1.51  --sup_to_prop_solver                    passive
% 7.94/1.51  --sup_prop_simpl_new                    true
% 7.94/1.51  --sup_prop_simpl_given                  true
% 7.94/1.51  --sup_fun_splitting                     false
% 7.94/1.51  --sup_smt_interval                      50000
% 7.94/1.51  
% 7.94/1.51  ------ Superposition Simplification Setup
% 7.94/1.51  
% 7.94/1.51  --sup_indices_passive                   []
% 7.94/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.94/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_full_bw                           [BwDemod]
% 7.94/1.51  --sup_immed_triv                        [TrivRules]
% 7.94/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_immed_bw_main                     []
% 7.94/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.94/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.51  
% 7.94/1.51  ------ Combination Options
% 7.94/1.51  
% 7.94/1.51  --comb_res_mult                         3
% 7.94/1.51  --comb_sup_mult                         2
% 7.94/1.51  --comb_inst_mult                        10
% 7.94/1.51  
% 7.94/1.51  ------ Debug Options
% 7.94/1.51  
% 7.94/1.51  --dbg_backtrace                         false
% 7.94/1.51  --dbg_dump_prop_clauses                 false
% 7.94/1.51  --dbg_dump_prop_clauses_file            -
% 7.94/1.51  --dbg_out_stat                          false
% 7.94/1.51  ------ Parsing...
% 7.94/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.51  ------ Proving...
% 7.94/1.51  ------ Problem Properties 
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  clauses                                 43
% 7.94/1.51  conjectures                             5
% 7.94/1.51  EPR                                     12
% 7.94/1.51  Horn                                    26
% 7.94/1.51  unary                                   5
% 7.94/1.51  binary                                  7
% 7.94/1.51  lits                                    157
% 7.94/1.51  lits eq                                 22
% 7.94/1.51  fd_pure                                 0
% 7.94/1.51  fd_pseudo                               0
% 7.94/1.51  fd_cond                                 0
% 7.94/1.51  fd_pseudo_cond                          5
% 7.94/1.51  AC symbols                              0
% 7.94/1.51  
% 7.94/1.51  ------ Schedule dynamic 5 is on 
% 7.94/1.51  
% 7.94/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  ------ 
% 7.94/1.51  Current options:
% 7.94/1.51  ------ 
% 7.94/1.51  
% 7.94/1.51  ------ Input Options
% 7.94/1.51  
% 7.94/1.51  --out_options                           all
% 7.94/1.51  --tptp_safe_out                         true
% 7.94/1.51  --problem_path                          ""
% 7.94/1.51  --include_path                          ""
% 7.94/1.51  --clausifier                            res/vclausify_rel
% 7.94/1.51  --clausifier_options                    --mode clausify
% 7.94/1.51  --stdin                                 false
% 7.94/1.51  --stats_out                             all
% 7.94/1.51  
% 7.94/1.51  ------ General Options
% 7.94/1.51  
% 7.94/1.51  --fof                                   false
% 7.94/1.51  --time_out_real                         305.
% 7.94/1.51  --time_out_virtual                      -1.
% 7.94/1.51  --symbol_type_check                     false
% 7.94/1.51  --clausify_out                          false
% 7.94/1.51  --sig_cnt_out                           false
% 7.94/1.51  --trig_cnt_out                          false
% 7.94/1.51  --trig_cnt_out_tolerance                1.
% 7.94/1.51  --trig_cnt_out_sk_spl                   false
% 7.94/1.51  --abstr_cl_out                          false
% 7.94/1.51  
% 7.94/1.51  ------ Global Options
% 7.94/1.51  
% 7.94/1.51  --schedule                              default
% 7.94/1.51  --add_important_lit                     false
% 7.94/1.51  --prop_solver_per_cl                    1000
% 7.94/1.51  --min_unsat_core                        false
% 7.94/1.51  --soft_assumptions                      false
% 7.94/1.51  --soft_lemma_size                       3
% 7.94/1.51  --prop_impl_unit_size                   0
% 7.94/1.51  --prop_impl_unit                        []
% 7.94/1.51  --share_sel_clauses                     true
% 7.94/1.51  --reset_solvers                         false
% 7.94/1.51  --bc_imp_inh                            [conj_cone]
% 7.94/1.51  --conj_cone_tolerance                   3.
% 7.94/1.51  --extra_neg_conj                        none
% 7.94/1.51  --large_theory_mode                     true
% 7.94/1.51  --prolific_symb_bound                   200
% 7.94/1.51  --lt_threshold                          2000
% 7.94/1.51  --clause_weak_htbl                      true
% 7.94/1.51  --gc_record_bc_elim                     false
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing Options
% 7.94/1.51  
% 7.94/1.51  --preprocessing_flag                    true
% 7.94/1.51  --time_out_prep_mult                    0.1
% 7.94/1.51  --splitting_mode                        input
% 7.94/1.51  --splitting_grd                         true
% 7.94/1.51  --splitting_cvd                         false
% 7.94/1.51  --splitting_cvd_svl                     false
% 7.94/1.51  --splitting_nvd                         32
% 7.94/1.51  --sub_typing                            true
% 7.94/1.51  --prep_gs_sim                           true
% 7.94/1.51  --prep_unflatten                        true
% 7.94/1.51  --prep_res_sim                          true
% 7.94/1.51  --prep_upred                            true
% 7.94/1.51  --prep_sem_filter                       exhaustive
% 7.94/1.51  --prep_sem_filter_out                   false
% 7.94/1.51  --pred_elim                             true
% 7.94/1.51  --res_sim_input                         true
% 7.94/1.51  --eq_ax_congr_red                       true
% 7.94/1.51  --pure_diseq_elim                       true
% 7.94/1.51  --brand_transform                       false
% 7.94/1.51  --non_eq_to_eq                          false
% 7.94/1.51  --prep_def_merge                        true
% 7.94/1.51  --prep_def_merge_prop_impl              false
% 7.94/1.51  --prep_def_merge_mbd                    true
% 7.94/1.51  --prep_def_merge_tr_red                 false
% 7.94/1.51  --prep_def_merge_tr_cl                  false
% 7.94/1.51  --smt_preprocessing                     true
% 7.94/1.51  --smt_ac_axioms                         fast
% 7.94/1.51  --preprocessed_out                      false
% 7.94/1.51  --preprocessed_stats                    false
% 7.94/1.51  
% 7.94/1.51  ------ Abstraction refinement Options
% 7.94/1.51  
% 7.94/1.51  --abstr_ref                             []
% 7.94/1.51  --abstr_ref_prep                        false
% 7.94/1.51  --abstr_ref_until_sat                   false
% 7.94/1.51  --abstr_ref_sig_restrict                funpre
% 7.94/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.94/1.51  --abstr_ref_under                       []
% 7.94/1.51  
% 7.94/1.51  ------ SAT Options
% 7.94/1.51  
% 7.94/1.51  --sat_mode                              false
% 7.94/1.51  --sat_fm_restart_options                ""
% 7.94/1.51  --sat_gr_def                            false
% 7.94/1.51  --sat_epr_types                         true
% 7.94/1.51  --sat_non_cyclic_types                  false
% 7.94/1.51  --sat_finite_models                     false
% 7.94/1.51  --sat_fm_lemmas                         false
% 7.94/1.51  --sat_fm_prep                           false
% 7.94/1.51  --sat_fm_uc_incr                        true
% 7.94/1.51  --sat_out_model                         small
% 7.94/1.51  --sat_out_clauses                       false
% 7.94/1.51  
% 7.94/1.51  ------ QBF Options
% 7.94/1.51  
% 7.94/1.51  --qbf_mode                              false
% 7.94/1.51  --qbf_elim_univ                         false
% 7.94/1.51  --qbf_dom_inst                          none
% 7.94/1.51  --qbf_dom_pre_inst                      false
% 7.94/1.51  --qbf_sk_in                             false
% 7.94/1.51  --qbf_pred_elim                         true
% 7.94/1.51  --qbf_split                             512
% 7.94/1.51  
% 7.94/1.51  ------ BMC1 Options
% 7.94/1.51  
% 7.94/1.51  --bmc1_incremental                      false
% 7.94/1.51  --bmc1_axioms                           reachable_all
% 7.94/1.51  --bmc1_min_bound                        0
% 7.94/1.51  --bmc1_max_bound                        -1
% 7.94/1.51  --bmc1_max_bound_default                -1
% 7.94/1.51  --bmc1_symbol_reachability              true
% 7.94/1.51  --bmc1_property_lemmas                  false
% 7.94/1.51  --bmc1_k_induction                      false
% 7.94/1.51  --bmc1_non_equiv_states                 false
% 7.94/1.51  --bmc1_deadlock                         false
% 7.94/1.51  --bmc1_ucm                              false
% 7.94/1.51  --bmc1_add_unsat_core                   none
% 7.94/1.51  --bmc1_unsat_core_children              false
% 7.94/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.94/1.51  --bmc1_out_stat                         full
% 7.94/1.51  --bmc1_ground_init                      false
% 7.94/1.51  --bmc1_pre_inst_next_state              false
% 7.94/1.51  --bmc1_pre_inst_state                   false
% 7.94/1.51  --bmc1_pre_inst_reach_state             false
% 7.94/1.51  --bmc1_out_unsat_core                   false
% 7.94/1.51  --bmc1_aig_witness_out                  false
% 7.94/1.51  --bmc1_verbose                          false
% 7.94/1.51  --bmc1_dump_clauses_tptp                false
% 7.94/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.94/1.51  --bmc1_dump_file                        -
% 7.94/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.94/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.94/1.51  --bmc1_ucm_extend_mode                  1
% 7.94/1.51  --bmc1_ucm_init_mode                    2
% 7.94/1.51  --bmc1_ucm_cone_mode                    none
% 7.94/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.94/1.51  --bmc1_ucm_relax_model                  4
% 7.94/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.94/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.94/1.51  --bmc1_ucm_layered_model                none
% 7.94/1.51  --bmc1_ucm_max_lemma_size               10
% 7.94/1.51  
% 7.94/1.51  ------ AIG Options
% 7.94/1.51  
% 7.94/1.51  --aig_mode                              false
% 7.94/1.51  
% 7.94/1.51  ------ Instantiation Options
% 7.94/1.51  
% 7.94/1.51  --instantiation_flag                    true
% 7.94/1.51  --inst_sos_flag                         false
% 7.94/1.51  --inst_sos_phase                        true
% 7.94/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.94/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.94/1.51  --inst_lit_sel_side                     none
% 7.94/1.51  --inst_solver_per_active                1400
% 7.94/1.51  --inst_solver_calls_frac                1.
% 7.94/1.51  --inst_passive_queue_type               priority_queues
% 7.94/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.94/1.51  --inst_passive_queues_freq              [25;2]
% 7.94/1.51  --inst_dismatching                      true
% 7.94/1.51  --inst_eager_unprocessed_to_passive     true
% 7.94/1.51  --inst_prop_sim_given                   true
% 7.94/1.51  --inst_prop_sim_new                     false
% 7.94/1.51  --inst_subs_new                         false
% 7.94/1.51  --inst_eq_res_simp                      false
% 7.94/1.51  --inst_subs_given                       false
% 7.94/1.51  --inst_orphan_elimination               true
% 7.94/1.51  --inst_learning_loop_flag               true
% 7.94/1.51  --inst_learning_start                   3000
% 7.94/1.51  --inst_learning_factor                  2
% 7.94/1.51  --inst_start_prop_sim_after_learn       3
% 7.94/1.51  --inst_sel_renew                        solver
% 7.94/1.51  --inst_lit_activity_flag                true
% 7.94/1.51  --inst_restr_to_given                   false
% 7.94/1.51  --inst_activity_threshold               500
% 7.94/1.51  --inst_out_proof                        true
% 7.94/1.51  
% 7.94/1.51  ------ Resolution Options
% 7.94/1.51  
% 7.94/1.51  --resolution_flag                       false
% 7.94/1.51  --res_lit_sel                           adaptive
% 7.94/1.51  --res_lit_sel_side                      none
% 7.94/1.51  --res_ordering                          kbo
% 7.94/1.51  --res_to_prop_solver                    active
% 7.94/1.51  --res_prop_simpl_new                    false
% 7.94/1.51  --res_prop_simpl_given                  true
% 7.94/1.51  --res_passive_queue_type                priority_queues
% 7.94/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.94/1.51  --res_passive_queues_freq               [15;5]
% 7.94/1.51  --res_forward_subs                      full
% 7.94/1.51  --res_backward_subs                     full
% 7.94/1.51  --res_forward_subs_resolution           true
% 7.94/1.51  --res_backward_subs_resolution          true
% 7.94/1.51  --res_orphan_elimination                true
% 7.94/1.51  --res_time_limit                        2.
% 7.94/1.51  --res_out_proof                         true
% 7.94/1.51  
% 7.94/1.51  ------ Superposition Options
% 7.94/1.51  
% 7.94/1.51  --superposition_flag                    true
% 7.94/1.51  --sup_passive_queue_type                priority_queues
% 7.94/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.94/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.94/1.51  --demod_completeness_check              fast
% 7.94/1.51  --demod_use_ground                      true
% 7.94/1.51  --sup_to_prop_solver                    passive
% 7.94/1.51  --sup_prop_simpl_new                    true
% 7.94/1.51  --sup_prop_simpl_given                  true
% 7.94/1.51  --sup_fun_splitting                     false
% 7.94/1.51  --sup_smt_interval                      50000
% 7.94/1.51  
% 7.94/1.51  ------ Superposition Simplification Setup
% 7.94/1.51  
% 7.94/1.51  --sup_indices_passive                   []
% 7.94/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.94/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_full_bw                           [BwDemod]
% 7.94/1.51  --sup_immed_triv                        [TrivRules]
% 7.94/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_immed_bw_main                     []
% 7.94/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.94/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.51  
% 7.94/1.51  ------ Combination Options
% 7.94/1.51  
% 7.94/1.51  --comb_res_mult                         3
% 7.94/1.51  --comb_sup_mult                         2
% 7.94/1.51  --comb_inst_mult                        10
% 7.94/1.51  
% 7.94/1.51  ------ Debug Options
% 7.94/1.51  
% 7.94/1.51  --dbg_backtrace                         false
% 7.94/1.51  --dbg_dump_prop_clauses                 false
% 7.94/1.51  --dbg_dump_prop_clauses_file            -
% 7.94/1.51  --dbg_out_stat                          false
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  ------ Proving...
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  % SZS status Theorem for theBenchmark.p
% 7.94/1.51  
% 7.94/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.94/1.51  
% 7.94/1.51  fof(f12,axiom,(
% 7.94/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f42,plain,(
% 7.94/1.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.94/1.51    inference(ennf_transformation,[],[f12])).
% 7.94/1.51  
% 7.94/1.51  fof(f96,plain,(
% 7.94/1.51    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.94/1.51    inference(cnf_transformation,[],[f42])).
% 7.94/1.51  
% 7.94/1.51  fof(f19,axiom,(
% 7.94/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f55,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(ennf_transformation,[],[f19])).
% 7.94/1.51  
% 7.94/1.51  fof(f114,plain,(
% 7.94/1.51    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f55])).
% 7.94/1.51  
% 7.94/1.51  fof(f24,conjecture,(
% 7.94/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f25,negated_conjecture,(
% 7.94/1.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 7.94/1.51    inference(negated_conjecture,[],[f24])).
% 7.94/1.51  
% 7.94/1.51  fof(f61,plain,(
% 7.94/1.51    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.94/1.51    inference(ennf_transformation,[],[f25])).
% 7.94/1.51  
% 7.94/1.51  fof(f62,plain,(
% 7.94/1.51    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.94/1.51    inference(flattening,[],[f61])).
% 7.94/1.51  
% 7.94/1.51  fof(f74,plain,(
% 7.94/1.51    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.94/1.51    inference(nnf_transformation,[],[f62])).
% 7.94/1.51  
% 7.94/1.51  fof(f75,plain,(
% 7.94/1.51    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.94/1.51    inference(flattening,[],[f74])).
% 7.94/1.51  
% 7.94/1.51  fof(f77,plain,(
% 7.94/1.51    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK3) | ~m1_pre_topc(sK3,X0) | ~v1_tsep_1(sK3,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK3) | (m1_pre_topc(sK3,X0) & v1_tsep_1(sK3,X0))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.94/1.51    introduced(choice_axiom,[])).
% 7.94/1.51  
% 7.94/1.51  fof(f76,plain,(
% 7.94/1.51    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,X1) | ~m1_pre_topc(X1,sK2) | ~v1_tsep_1(X1,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,X1) | (m1_pre_topc(X1,sK2) & v1_tsep_1(X1,sK2))) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.94/1.51    introduced(choice_axiom,[])).
% 7.94/1.51  
% 7.94/1.51  fof(f78,plain,(
% 7.94/1.51    ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) | (m1_pre_topc(sK3,sK2) & v1_tsep_1(sK3,sK2))) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.94/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f75,f77,f76])).
% 7.94/1.51  
% 7.94/1.51  fof(f123,plain,(
% 7.94/1.51    m1_pre_topc(sK3,sK2)),
% 7.94/1.51    inference(cnf_transformation,[],[f78])).
% 7.94/1.51  
% 7.94/1.51  fof(f23,axiom,(
% 7.94/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f59,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.94/1.51    inference(ennf_transformation,[],[f23])).
% 7.94/1.51  
% 7.94/1.51  fof(f60,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.94/1.51    inference(flattening,[],[f59])).
% 7.94/1.51  
% 7.94/1.51  fof(f118,plain,(
% 7.94/1.51    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f60])).
% 7.94/1.51  
% 7.94/1.51  fof(f120,plain,(
% 7.94/1.51    v2_pre_topc(sK2)),
% 7.94/1.51    inference(cnf_transformation,[],[f78])).
% 7.94/1.51  
% 7.94/1.51  fof(f121,plain,(
% 7.94/1.51    l1_pre_topc(sK2)),
% 7.94/1.51    inference(cnf_transformation,[],[f78])).
% 7.94/1.51  
% 7.94/1.51  fof(f8,axiom,(
% 7.94/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f36,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(ennf_transformation,[],[f8])).
% 7.94/1.51  
% 7.94/1.51  fof(f90,plain,(
% 7.94/1.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f36])).
% 7.94/1.51  
% 7.94/1.51  fof(f5,axiom,(
% 7.94/1.51    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f32,plain,(
% 7.94/1.51    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(ennf_transformation,[],[f5])).
% 7.94/1.51  
% 7.94/1.51  fof(f33,plain,(
% 7.94/1.51    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(flattening,[],[f32])).
% 7.94/1.51  
% 7.94/1.51  fof(f86,plain,(
% 7.94/1.51    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f33])).
% 7.94/1.51  
% 7.94/1.51  fof(f113,plain,(
% 7.94/1.51    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f55])).
% 7.94/1.51  
% 7.94/1.51  fof(f95,plain,(
% 7.94/1.51    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.94/1.51    inference(cnf_transformation,[],[f42])).
% 7.94/1.51  
% 7.94/1.51  fof(f9,axiom,(
% 7.94/1.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f37,plain,(
% 7.94/1.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(ennf_transformation,[],[f9])).
% 7.94/1.51  
% 7.94/1.51  fof(f91,plain,(
% 7.94/1.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f37])).
% 7.94/1.51  
% 7.94/1.51  fof(f20,axiom,(
% 7.94/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f56,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(ennf_transformation,[],[f20])).
% 7.94/1.51  
% 7.94/1.51  fof(f115,plain,(
% 7.94/1.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f56])).
% 7.94/1.51  
% 7.94/1.51  fof(f17,axiom,(
% 7.94/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f51,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.94/1.51    inference(ennf_transformation,[],[f17])).
% 7.94/1.51  
% 7.94/1.51  fof(f52,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.51    inference(flattening,[],[f51])).
% 7.94/1.51  
% 7.94/1.51  fof(f73,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.51    inference(nnf_transformation,[],[f52])).
% 7.94/1.51  
% 7.94/1.51  fof(f109,plain,(
% 7.94/1.51    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f73])).
% 7.94/1.51  
% 7.94/1.51  fof(f119,plain,(
% 7.94/1.51    ~v2_struct_0(sK2)),
% 7.94/1.51    inference(cnf_transformation,[],[f78])).
% 7.94/1.51  
% 7.94/1.51  fof(f14,axiom,(
% 7.94/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f45,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(ennf_transformation,[],[f14])).
% 7.94/1.51  
% 7.94/1.51  fof(f46,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(flattening,[],[f45])).
% 7.94/1.51  
% 7.94/1.51  fof(f69,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(nnf_transformation,[],[f46])).
% 7.94/1.51  
% 7.94/1.51  fof(f70,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(rectify,[],[f69])).
% 7.94/1.51  
% 7.94/1.51  fof(f71,plain,(
% 7.94/1.51    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.94/1.51    introduced(choice_axiom,[])).
% 7.94/1.51  
% 7.94/1.51  fof(f72,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f70,f71])).
% 7.94/1.51  
% 7.94/1.51  fof(f103,plain,(
% 7.94/1.51    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f72])).
% 7.94/1.51  
% 7.94/1.51  fof(f126,plain,(
% 7.94/1.51    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2)),
% 7.94/1.51    inference(cnf_transformation,[],[f78])).
% 7.94/1.51  
% 7.94/1.51  fof(f104,plain,(
% 7.94/1.51    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK1(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f72])).
% 7.94/1.51  
% 7.94/1.51  fof(f13,axiom,(
% 7.94/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f43,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.94/1.51    inference(ennf_transformation,[],[f13])).
% 7.94/1.51  
% 7.94/1.51  fof(f44,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.51    inference(flattening,[],[f43])).
% 7.94/1.51  
% 7.94/1.51  fof(f65,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.51    inference(nnf_transformation,[],[f44])).
% 7.94/1.51  
% 7.94/1.51  fof(f66,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.51    inference(rectify,[],[f65])).
% 7.94/1.51  
% 7.94/1.51  fof(f67,plain,(
% 7.94/1.51    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.94/1.51    introduced(choice_axiom,[])).
% 7.94/1.51  
% 7.94/1.51  fof(f68,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f66,f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f97,plain,(
% 7.94/1.51    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f68])).
% 7.94/1.51  
% 7.94/1.51  fof(f127,plain,(
% 7.94/1.51    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.51    inference(equality_resolution,[],[f97])).
% 7.94/1.51  
% 7.94/1.51  fof(f128,plain,(
% 7.94/1.51    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.51    inference(equality_resolution,[],[f127])).
% 7.94/1.51  
% 7.94/1.51  fof(f16,axiom,(
% 7.94/1.51    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f49,plain,(
% 7.94/1.51    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.94/1.51    inference(ennf_transformation,[],[f16])).
% 7.94/1.51  
% 7.94/1.51  fof(f50,plain,(
% 7.94/1.51    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.51    inference(flattening,[],[f49])).
% 7.94/1.51  
% 7.94/1.51  fof(f106,plain,(
% 7.94/1.51    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f50])).
% 7.94/1.51  
% 7.94/1.51  fof(f107,plain,(
% 7.94/1.51    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f50])).
% 7.94/1.51  
% 7.94/1.51  fof(f108,plain,(
% 7.94/1.51    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f50])).
% 7.94/1.51  
% 7.94/1.51  fof(f6,axiom,(
% 7.94/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f34,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(ennf_transformation,[],[f6])).
% 7.94/1.51  
% 7.94/1.51  fof(f64,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(nnf_transformation,[],[f34])).
% 7.94/1.51  
% 7.94/1.51  fof(f88,plain,(
% 7.94/1.51    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f64])).
% 7.94/1.51  
% 7.94/1.51  fof(f15,axiom,(
% 7.94/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f47,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.94/1.51    inference(ennf_transformation,[],[f15])).
% 7.94/1.51  
% 7.94/1.51  fof(f48,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.51    inference(flattening,[],[f47])).
% 7.94/1.51  
% 7.94/1.51  fof(f105,plain,(
% 7.94/1.51    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f48])).
% 7.94/1.51  
% 7.94/1.51  fof(f18,axiom,(
% 7.94/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 7.94/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f53,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.94/1.51    inference(ennf_transformation,[],[f18])).
% 7.94/1.51  
% 7.94/1.51  fof(f54,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.94/1.51    inference(flattening,[],[f53])).
% 7.94/1.51  
% 7.94/1.51  fof(f112,plain,(
% 7.94/1.51    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f54])).
% 7.94/1.51  
% 7.94/1.51  fof(f110,plain,(
% 7.94/1.51    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f73])).
% 7.94/1.51  
% 7.94/1.51  fof(f87,plain,(
% 7.94/1.51    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f64])).
% 7.94/1.51  
% 7.94/1.51  fof(f101,plain,(
% 7.94/1.51    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f72])).
% 7.94/1.51  
% 7.94/1.51  fof(f129,plain,(
% 7.94/1.51    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(equality_resolution,[],[f101])).
% 7.94/1.51  
% 7.94/1.51  fof(f124,plain,(
% 7.94/1.51    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) | v1_tsep_1(sK3,sK2)),
% 7.94/1.51    inference(cnf_transformation,[],[f78])).
% 7.94/1.51  
% 7.94/1.51  cnf(c_16,plain,
% 7.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.94/1.51      | X2 = X0
% 7.94/1.51      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8297,plain,
% 7.94/1.51      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.94/1.51      | X2 = u1_pre_topc(X0)
% 7.94/1.51      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,u1_pre_topc(X0)) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_16]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9829,plain,
% 7.94/1.51      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.94/1.51      | X2 = u1_pre_topc(X0)
% 7.94/1.51      | g1_pre_topc(X3,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X0)) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8297]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_13954,plain,
% 7.94/1.51      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.94/1.51      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X0))
% 7.94/1.51      | u1_pre_topc(X2) = u1_pre_topc(X0) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_9829]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_35784,plain,
% 7.94/1.51      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.94/1.51      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(sK2))
% 7.94/1.51      | u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_13954]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_35797,plain,
% 7.94/1.51      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.94/1.51      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.94/1.51      | u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_35784]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_34,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.94/1.51      | ~ l1_pre_topc(X1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f114]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7576,plain,
% 7.94/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.94/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_43,negated_conjecture,
% 7.94/1.51      ( m1_pre_topc(sK3,sK2) ),
% 7.94/1.51      inference(cnf_transformation,[],[f123]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7571,plain,
% 7.94/1.51      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_39,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ m1_pre_topc(X2,X0)
% 7.94/1.51      | m1_pre_topc(X2,X1)
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f118]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7572,plain,
% 7.94/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.94/1.51      | m1_pre_topc(X2,X0) != iProver_top
% 7.94/1.51      | m1_pre_topc(X2,X1) = iProver_top
% 7.94/1.51      | v2_pre_topc(X1) != iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_10057,plain,
% 7.94/1.51      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.94/1.51      | m1_pre_topc(X0,sK2) = iProver_top
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_7571,c_7572]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_46,negated_conjecture,
% 7.94/1.51      ( v2_pre_topc(sK2) ),
% 7.94/1.51      inference(cnf_transformation,[],[f120]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_49,plain,
% 7.94/1.51      ( v2_pre_topc(sK2) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_45,negated_conjecture,
% 7.94/1.51      ( l1_pre_topc(sK2) ),
% 7.94/1.51      inference(cnf_transformation,[],[f121]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_50,plain,
% 7.94/1.51      ( l1_pre_topc(sK2) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_10348,plain,
% 7.94/1.51      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.94/1.51      | m1_pre_topc(X0,sK2) = iProver_top ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_10057,c_49,c_50]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_10356,plain,
% 7.94/1.51      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.94/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_7576,c_10348]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_11,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7593,plain,
% 7.94/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top
% 7.94/1.51      | l1_pre_topc(X0) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8099,plain,
% 7.94/1.51      ( l1_pre_topc(sK3) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_7571,c_7593]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_10368,plain,
% 7.94/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
% 7.94/1.51      | m1_pre_topc(X0,sK3) != iProver_top ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_10356,c_50,c_8099]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_10369,plain,
% 7.94/1.51      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.94/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top ),
% 7.94/1.51      inference(renaming,[status(thm)],[c_10368]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8978,plain,
% 7.94/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top
% 7.94/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_7576,c_7593]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9003,plain,
% 7.94/1.51      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_7571,c_8978]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9382,plain,
% 7.94/1.51      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_9003,c_50]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7,plain,
% 7.94/1.51      ( ~ l1_pre_topc(X0)
% 7.94/1.51      | ~ v1_pre_topc(X0)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 7.94/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7596,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 7.94/1.51      | l1_pre_topc(X0) != iProver_top
% 7.94/1.51      | v1_pre_topc(X0) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9387,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
% 7.94/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_9382,c_7596]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_35,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.94/1.51      inference(cnf_transformation,[],[f113]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7575,plain,
% 7.94/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top
% 7.94/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8756,plain,
% 7.94/1.51      ( l1_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_7571,c_7575]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9480,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_9387,c_50,c_8756]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_17,plain,
% 7.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.94/1.51      | X2 = X1
% 7.94/1.51      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7588,plain,
% 7.94/1.51      ( X0 = X1
% 7.94/1.51      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 7.94/1.51      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9488,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 7.94/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
% 7.94/1.51      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_9480,c_7588]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9651,plain,
% 7.94/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 7.94/1.51      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.94/1.51      inference(equality_resolution,[status(thm)],[c_9488]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_12,plain,
% 7.94/1.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.94/1.51      | ~ l1_pre_topc(X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7592,plain,
% 7.94/1.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 7.94/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9487,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 7.94/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
% 7.94/1.51      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_9480,c_7588]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9532,plain,
% 7.94/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 7.94/1.51      | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
% 7.94/1.51      inference(equality_resolution,[status(thm)],[c_9487]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9767,plain,
% 7.94/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 7.94/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_7592,c_9532]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_10668,plain,
% 7.94/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3) ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_9651,c_50,c_8099,c_9767]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_36,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.94/1.51      | ~ l1_pre_topc(X1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f115]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7574,plain,
% 7.94/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.94/1.51      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_10714,plain,
% 7.94/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top
% 7.94/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.94/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_10668,c_7574]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_14404,plain,
% 7.94/1.51      ( m1_pre_topc(sK3,sK3) != iProver_top
% 7.94/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_10369,c_10714]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_52,plain,
% 7.94/1.51      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8369,plain,
% 7.94/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.94/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.94/1.51      | ~ l1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_36]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8370,plain,
% 7.94/1.51      ( m1_pre_topc(sK3,sK2) != iProver_top
% 7.94/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_8369]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_14508,plain,
% 7.94/1.51      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_14404,c_50,c_52,c_8370]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_31,plain,
% 7.94/1.51      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | v2_struct_0(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f109]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7579,plain,
% 7.94/1.51      ( k5_tmap_1(X0,X1) = u1_pre_topc(X0)
% 7.94/1.51      | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
% 7.94/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.94/1.51      | v2_pre_topc(X0) != iProver_top
% 7.94/1.51      | v2_struct_0(X0) = iProver_top
% 7.94/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_14517,plain,
% 7.94/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
% 7.94/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v2_struct_0(sK2) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_14508,c_7579]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_47,negated_conjecture,
% 7.94/1.51      ( ~ v2_struct_0(sK2) ),
% 7.94/1.51      inference(cnf_transformation,[],[f119]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_48,plain,
% 7.94/1.51      ( v2_struct_0(sK2) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_23,plain,
% 7.94/1.51      ( v1_tsep_1(X0,X1)
% 7.94/1.51      | ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | sK1(X1,X0) = u1_struct_0(X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f103]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_40,negated_conjecture,
% 7.94/1.51      ( ~ v1_tsep_1(sK3,sK2)
% 7.94/1.51      | ~ m1_pre_topc(sK3,sK2)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(cnf_transformation,[],[f126]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_384,plain,
% 7.94/1.51      ( ~ v1_tsep_1(sK3,sK2)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(prop_impl,[status(thm)],[c_43,c_40]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_788,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | sK1(X1,X0) = u1_struct_0(X0)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 7.94/1.51      | sK3 != X0
% 7.94/1.51      | sK2 != X1 ),
% 7.94/1.51      inference(resolution_lifted,[status(thm)],[c_23,c_384]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_789,plain,
% 7.94/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | sK1(sK2,sK3) = u1_struct_0(sK3)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(unflattening,[status(thm)],[c_788]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_791,plain,
% 7.94/1.51      ( sK1(sK2,sK3) = u1_struct_0(sK3)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_789,c_45,c_43]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_22,plain,
% 7.94/1.51      ( v1_tsep_1(X0,X1)
% 7.94/1.51      | ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ v3_pre_topc(sK1(X1,X0),X1)
% 7.94/1.51      | ~ l1_pre_topc(X1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f104]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_799,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ v3_pre_topc(sK1(X1,X0),X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 7.94/1.51      | sK3 != X0
% 7.94/1.51      | sK2 != X1 ),
% 7.94/1.51      inference(resolution_lifted,[status(thm)],[c_22,c_384]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_800,plain,
% 7.94/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.94/1.51      | ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(unflattening,[status(thm)],[c_799]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_802,plain,
% 7.94/1.51      ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_800,c_45,c_43]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_804,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 7.94/1.51      | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6812,plain,
% 7.94/1.51      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 7.94/1.51      theory(equality) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6828,plain,
% 7.94/1.51      ( u1_struct_0(sK2) = u1_struct_0(sK2) | sK2 != sK2 ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_6812]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6813,plain,
% 7.94/1.51      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 7.94/1.51      theory(equality) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6829,plain,
% 7.94/1.51      ( u1_pre_topc(sK2) = u1_pre_topc(sK2) | sK2 != sK2 ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_6813]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6806,plain,( X0 = X0 ),theory(equality) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6841,plain,
% 7.94/1.51      ( sK2 = sK2 ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_6806]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8180,plain,
% 7.94/1.51      ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
% 7.94/1.51      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | v2_struct_0(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_31]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8184,plain,
% 7.94/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
% 7.94/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 7.94/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v2_struct_0(sK2) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_8180]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8894,plain,
% 7.94/1.51      ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_6806]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_21,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 7.94/1.51      | v2_struct_0(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 7.94/1.51      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 7.94/1.51      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f128]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_29,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | v2_struct_0(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | v1_pre_topc(k8_tmap_1(X1,X0)) ),
% 7.94/1.51      inference(cnf_transformation,[],[f106]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_28,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | v2_pre_topc(k8_tmap_1(X1,X0))
% 7.94/1.51      | v2_struct_0(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f107]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_27,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | v2_struct_0(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 7.94/1.51      inference(cnf_transformation,[],[f108]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_301,plain,
% 7.94/1.51      ( ~ v2_pre_topc(X1)
% 7.94/1.51      | ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | v2_struct_0(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_21,c_36,c_29,c_28,c_27]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_302,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | v2_struct_0(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 7.94/1.51      inference(renaming,[status(thm)],[c_301]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9302,plain,
% 7.94/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | v2_struct_0(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_302]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6817,plain,
% 7.94/1.51      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.94/1.51      theory(equality) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8086,plain,
% 7.94/1.51      ( v3_pre_topc(X0,X1)
% 7.94/1.51      | ~ v3_pre_topc(u1_struct_0(X2),X3)
% 7.94/1.51      | X1 != X3
% 7.94/1.51      | X0 != u1_struct_0(X2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_6817]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9715,plain,
% 7.94/1.51      ( v3_pre_topc(sK1(sK2,sK3),X0)
% 7.94/1.51      | ~ v3_pre_topc(u1_struct_0(sK3),X1)
% 7.94/1.51      | X0 != X1
% 7.94/1.51      | sK1(sK2,sK3) != u1_struct_0(sK3) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8086]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9716,plain,
% 7.94/1.51      ( X0 != X1
% 7.94/1.51      | sK1(sK2,sK3) != u1_struct_0(sK3)
% 7.94/1.51      | v3_pre_topc(sK1(sK2,sK3),X0) = iProver_top
% 7.94/1.51      | v3_pre_topc(u1_struct_0(sK3),X1) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_9715]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9718,plain,
% 7.94/1.51      ( sK1(sK2,sK3) != u1_struct_0(sK3)
% 7.94/1.51      | sK2 != sK2
% 7.94/1.51      | v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
% 7.94/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_9716]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6807,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8408,plain,
% 7.94/1.51      ( X0 != X1 | u1_pre_topc(sK2) != X1 | u1_pre_topc(sK2) = X0 ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_6807]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8851,plain,
% 7.94/1.51      ( X0 != u1_pre_topc(sK2)
% 7.94/1.51      | u1_pre_topc(sK2) = X0
% 7.94/1.51      | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8408]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_10091,plain,
% 7.94/1.51      ( k5_tmap_1(sK2,u1_struct_0(X0)) != u1_pre_topc(sK2)
% 7.94/1.51      | u1_pre_topc(sK2) = k5_tmap_1(sK2,u1_struct_0(X0))
% 7.94/1.51      | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8851]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_11277,plain,
% 7.94/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK3)) != u1_pre_topc(sK2)
% 7.94/1.51      | u1_pre_topc(sK2) = k5_tmap_1(sK2,u1_struct_0(sK3))
% 7.94/1.51      | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_10091]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8605,plain,
% 7.94/1.51      ( X0 != X1 | k8_tmap_1(X2,X3) != X1 | k8_tmap_1(X2,X3) = X0 ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_6807]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9192,plain,
% 7.94/1.51      ( X0 != k8_tmap_1(X1,X2)
% 7.94/1.51      | k8_tmap_1(X1,X2) = X0
% 7.94/1.51      | k8_tmap_1(X1,X2) != k8_tmap_1(X1,X2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8605]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_10326,plain,
% 7.94/1.51      ( k6_tmap_1(X0,u1_struct_0(X1)) != k8_tmap_1(X0,X1)
% 7.94/1.51      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
% 7.94/1.51      | k8_tmap_1(X0,X1) != k8_tmap_1(X0,X1) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_9192]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_15666,plain,
% 7.94/1.51      ( k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 7.94/1.51      | k8_tmap_1(sK2,sK3) = k6_tmap_1(sK2,u1_struct_0(sK3))
% 7.94/1.51      | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_10326]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8,plain,
% 7.94/1.51      ( v3_pre_topc(X0,X1)
% 7.94/1.51      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.94/1.51      | ~ l1_pre_topc(X1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7595,plain,
% 7.94/1.51      ( v3_pre_topc(X0,X1) = iProver_top
% 7.94/1.51      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 7.94/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_14515,plain,
% 7.94/1.51      ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
% 7.94/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_14508,c_7595]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8181,plain,
% 7.94/1.51      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.94/1.51      | ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
% 7.94/1.51      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.94/1.51      | ~ l1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8182,plain,
% 7.94/1.51      ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
% 7.94/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 7.94/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_8181]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_17300,plain,
% 7.94/1.51      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 7.94/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_14515,c_50,c_52,c_8182,c_8370]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_17301,plain,
% 7.94/1.51      ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
% 7.94/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
% 7.94/1.51      inference(renaming,[status(thm)],[c_17300]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8396,plain,
% 7.94/1.51      ( k8_tmap_1(sK2,sK3) != X0
% 7.94/1.51      | k8_tmap_1(sK2,sK3) = g1_pre_topc(X1,X2)
% 7.94/1.51      | g1_pre_topc(X1,X2) != X0 ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_6807]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_15667,plain,
% 7.94/1.51      ( k8_tmap_1(sK2,sK3) != k6_tmap_1(sK2,u1_struct_0(sK3))
% 7.94/1.51      | k8_tmap_1(sK2,sK3) = g1_pre_topc(X0,X1)
% 7.94/1.51      | g1_pre_topc(X0,X1) != k6_tmap_1(sK2,u1_struct_0(sK3)) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8396]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_18877,plain,
% 7.94/1.51      ( k8_tmap_1(sK2,sK3) != k6_tmap_1(sK2,u1_struct_0(sK3))
% 7.94/1.51      | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3)))
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3))) != k6_tmap_1(sK2,u1_struct_0(sK3)) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_15667]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_26,plain,
% 7.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | v2_struct_0(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f105]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8120,plain,
% 7.94/1.51      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | v2_struct_0(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,u1_struct_0(X0))) = k6_tmap_1(X1,u1_struct_0(X0)) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_26]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_18878,plain,
% 7.94/1.51      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | v2_struct_0(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3))) = k6_tmap_1(sK2,u1_struct_0(sK3)) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8120]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8033,plain,
% 7.94/1.51      ( k8_tmap_1(sK2,sK3) != X0
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_6807]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8197,plain,
% 7.94/1.51      ( k8_tmap_1(sK2,sK3) != g1_pre_topc(X0,X1)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8033]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_19956,plain,
% 7.94/1.51      ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3)))
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3))) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8197]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6814,plain,
% 7.94/1.51      ( X0 != X1 | X2 != X3 | g1_pre_topc(X0,X2) = g1_pre_topc(X1,X3) ),
% 7.94/1.51      theory(equality) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8587,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(X1,X2)
% 7.94/1.51      | u1_pre_topc(X0) != X2
% 7.94/1.51      | u1_struct_0(X0) != X1 ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_6814]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_13776,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(X0,k5_tmap_1(sK2,u1_struct_0(X1)))
% 7.94/1.51      | u1_pre_topc(sK2) != k5_tmap_1(sK2,u1_struct_0(X1))
% 7.94/1.51      | u1_struct_0(sK2) != X0 ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8587]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_18329,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(X0)))
% 7.94/1.51      | u1_pre_topc(sK2) != k5_tmap_1(sK2,u1_struct_0(X0))
% 7.94/1.51      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_13776]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_29050,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK3)))
% 7.94/1.51      | u1_pre_topc(sK2) != k5_tmap_1(sK2,u1_struct_0(sK3))
% 7.94/1.51      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_18329]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_29676,plain,
% 7.94/1.51      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_14517,c_47,c_48,c_46,c_49,c_45,c_50,c_43,c_52,c_791,
% 7.94/1.51                 c_804,c_6828,c_6829,c_6841,c_8184,c_8369,c_8370,c_8894,
% 7.94/1.51                 c_9302,c_9718,c_11277,c_15666,c_17301,c_18877,c_18878,
% 7.94/1.51                 c_19956,c_29050]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_32,plain,
% 7.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | v2_struct_0(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f112]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7578,plain,
% 7.94/1.51      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
% 7.94/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.94/1.51      | v2_pre_topc(X0) != iProver_top
% 7.94/1.51      | v2_struct_0(X0) = iProver_top
% 7.94/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_14519,plain,
% 7.94/1.51      ( u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK3))) = k5_tmap_1(sK2,u1_struct_0(sK3))
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v2_struct_0(sK2) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_14508,c_7578]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7566,plain,
% 7.94/1.51      ( k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 7.94/1.51      | m1_pre_topc(X1,X0) != iProver_top
% 7.94/1.51      | v2_pre_topc(X0) != iProver_top
% 7.94/1.51      | v2_struct_0(X0) = iProver_top
% 7.94/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_11940,plain,
% 7.94/1.51      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3)
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v2_struct_0(sK2) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_7571,c_7566]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_12409,plain,
% 7.94/1.51      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_11940,c_47,c_46,c_45,c_43,c_9302]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_14534,plain,
% 7.94/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v2_struct_0(sK2) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(light_normalisation,[status(thm)],[c_14519,c_12409]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_15041,plain,
% 7.94/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_14534,c_48,c_49,c_50]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_30,plain,
% 7.94/1.51      ( r2_hidden(X0,u1_pre_topc(X1))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | v2_struct_0(X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f110]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7580,plain,
% 7.94/1.51      ( k5_tmap_1(X0,X1) != u1_pre_topc(X0)
% 7.94/1.51      | r2_hidden(X1,u1_pre_topc(X0)) = iProver_top
% 7.94/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.94/1.51      | v2_pre_topc(X0) != iProver_top
% 7.94/1.51      | v2_struct_0(X0) = iProver_top
% 7.94/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_15044,plain,
% 7.94/1.51      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
% 7.94/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 7.94/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v2_struct_0(sK2) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_15041,c_7580]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_20714,plain,
% 7.94/1.51      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
% 7.94/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_15044,c_48,c_49,c_50,c_52,c_8370]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9,plain,
% 7.94/1.51      ( ~ v3_pre_topc(X0,X1)
% 7.94/1.51      | r2_hidden(X0,u1_pre_topc(X1))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.94/1.51      | ~ l1_pre_topc(X1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7594,plain,
% 7.94/1.51      ( v3_pre_topc(X0,X1) != iProver_top
% 7.94/1.51      | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
% 7.94/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_14516,plain,
% 7.94/1.51      ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
% 7.94/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_14508,c_7594]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8035,plain,
% 7.94/1.51      ( ~ v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.94/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
% 7.94/1.51      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.94/1.51      | ~ l1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8036,plain,
% 7.94/1.51      ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
% 7.94/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 7.94/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_8035]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_17307,plain,
% 7.94/1.51      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 7.94/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_14516,c_50,c_52,c_8036,c_8370]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_17308,plain,
% 7.94/1.51      ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
% 7.94/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
% 7.94/1.51      inference(renaming,[status(thm)],[c_17307]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_12642,plain,
% 7.94/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | v2_struct_0(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_29]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_10652,plain,
% 7.94/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | v2_struct_0(sK2)
% 7.94/1.51      | l1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.94/1.51      | ~ l1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_27]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8579,plain,
% 7.94/1.51      ( X0 != X1
% 7.94/1.51      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
% 7.94/1.51      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X0 ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_6807]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9165,plain,
% 7.94/1.51      ( X0 != k8_tmap_1(X1,X2)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X2)),u1_pre_topc(k8_tmap_1(X1,X2))) = X0
% 7.94/1.51      | g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X2)),u1_pre_topc(k8_tmap_1(X1,X2))) != k8_tmap_1(X1,X2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8579]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_10481,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_9165]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8038,plain,
% 7.94/1.51      ( ~ l1_pre_topc(k8_tmap_1(X0,X1))
% 7.94/1.51      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
% 7.94/1.51      | g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9312,plain,
% 7.94/1.51      ( ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.94/1.51      | ~ v1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.94/1.51      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_8038]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_25,plain,
% 7.94/1.51      ( ~ v1_tsep_1(X0,X1)
% 7.94/1.51      | ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | v3_pre_topc(u1_struct_0(X0),X1)
% 7.94/1.51      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.94/1.51      | ~ l1_pre_topc(X1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f129]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_291,plain,
% 7.94/1.51      ( v3_pre_topc(u1_struct_0(X0),X1)
% 7.94/1.51      | ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | ~ v1_tsep_1(X0,X1)
% 7.94/1.51      | ~ l1_pre_topc(X1) ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_25,c_36]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_292,plain,
% 7.94/1.51      ( ~ v1_tsep_1(X0,X1)
% 7.94/1.51      | ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | v3_pre_topc(u1_struct_0(X0),X1)
% 7.94/1.51      | ~ l1_pre_topc(X1) ),
% 7.94/1.51      inference(renaming,[status(thm)],[c_291]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_42,negated_conjecture,
% 7.94/1.51      ( v1_tsep_1(sK3,sK2)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(cnf_transformation,[],[f124]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_386,plain,
% 7.94/1.51      ( v1_tsep_1(sK3,sK2)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(prop_impl,[status(thm)],[c_42]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_813,plain,
% 7.94/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.94/1.51      | v3_pre_topc(u1_struct_0(X0),X1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.94/1.51      | sK3 != X0
% 7.94/1.51      | sK2 != X1 ),
% 7.94/1.51      inference(resolution_lifted,[status(thm)],[c_292,c_386]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_814,plain,
% 7.94/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.94/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(unflattening,[status(thm)],[c_813]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_816,plain,
% 7.94/1.51      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.94/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_814,c_45,c_43]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_818,plain,
% 7.94/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.94/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_134,plain,
% 7.94/1.51      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.94/1.51      | ~ l1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_12]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(contradiction,plain,
% 7.94/1.51      ( $false ),
% 7.94/1.51      inference(minisat,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_35797,c_29676,c_20714,c_17308,c_12642,c_10652,c_10481,
% 7.94/1.51                 c_9312,c_818,c_134,c_43,c_45,c_46,c_47]) ).
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.94/1.51  
% 7.94/1.51  ------                               Statistics
% 7.94/1.51  
% 7.94/1.51  ------ General
% 7.94/1.51  
% 7.94/1.51  abstr_ref_over_cycles:                  0
% 7.94/1.51  abstr_ref_under_cycles:                 0
% 7.94/1.51  gc_basic_clause_elim:                   0
% 7.94/1.51  forced_gc_time:                         0
% 7.94/1.51  parsing_time:                           0.015
% 7.94/1.51  unif_index_cands_time:                  0.
% 7.94/1.51  unif_index_add_time:                    0.
% 7.94/1.51  orderings_time:                         0.
% 7.94/1.51  out_proof_time:                         0.018
% 7.94/1.51  total_time:                             0.899
% 7.94/1.51  num_of_symbols:                         54
% 7.94/1.51  num_of_terms:                           20915
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing
% 7.94/1.51  
% 7.94/1.51  num_of_splits:                          0
% 7.94/1.51  num_of_split_atoms:                     0
% 7.94/1.51  num_of_reused_defs:                     0
% 7.94/1.51  num_eq_ax_congr_red:                    25
% 7.94/1.51  num_of_sem_filtered_clauses:            1
% 7.94/1.51  num_of_subtypes:                        0
% 7.94/1.51  monotx_restored_types:                  0
% 7.94/1.51  sat_num_of_epr_types:                   0
% 7.94/1.51  sat_num_of_non_cyclic_types:            0
% 7.94/1.51  sat_guarded_non_collapsed_types:        0
% 7.94/1.51  num_pure_diseq_elim:                    0
% 7.94/1.51  simp_replaced_by:                       0
% 7.94/1.51  res_preprocessed:                       211
% 7.94/1.51  prep_upred:                             0
% 7.94/1.51  prep_unflattend:                        257
% 7.94/1.51  smt_new_axioms:                         0
% 7.94/1.51  pred_elim_cands:                        9
% 7.94/1.51  pred_elim:                              3
% 7.94/1.51  pred_elim_cl:                           2
% 7.94/1.51  pred_elim_cycles:                       10
% 7.94/1.51  merged_defs:                            2
% 7.94/1.51  merged_defs_ncl:                        0
% 7.94/1.51  bin_hyper_res:                          2
% 7.94/1.51  prep_cycles:                            4
% 7.94/1.51  pred_elim_time:                         0.124
% 7.94/1.51  splitting_time:                         0.
% 7.94/1.51  sem_filter_time:                        0.
% 7.94/1.51  monotx_time:                            0.
% 7.94/1.51  subtype_inf_time:                       0.
% 7.94/1.51  
% 7.94/1.51  ------ Problem properties
% 7.94/1.51  
% 7.94/1.51  clauses:                                43
% 7.94/1.51  conjectures:                            5
% 7.94/1.51  epr:                                    12
% 7.94/1.51  horn:                                   26
% 7.94/1.51  ground:                                 9
% 7.94/1.51  unary:                                  5
% 7.94/1.51  binary:                                 7
% 7.94/1.51  lits:                                   157
% 7.94/1.51  lits_eq:                                22
% 7.94/1.51  fd_pure:                                0
% 7.94/1.51  fd_pseudo:                              0
% 7.94/1.51  fd_cond:                                0
% 7.94/1.51  fd_pseudo_cond:                         5
% 7.94/1.51  ac_symbols:                             0
% 7.94/1.51  
% 7.94/1.51  ------ Propositional Solver
% 7.94/1.51  
% 7.94/1.51  prop_solver_calls:                      32
% 7.94/1.51  prop_fast_solver_calls:                 4388
% 7.94/1.51  smt_solver_calls:                       0
% 7.94/1.51  smt_fast_solver_calls:                  0
% 7.94/1.51  prop_num_of_clauses:                    7542
% 7.94/1.51  prop_preprocess_simplified:             17535
% 7.94/1.51  prop_fo_subsumed:                       263
% 7.94/1.51  prop_solver_time:                       0.
% 7.94/1.51  smt_solver_time:                        0.
% 7.94/1.51  smt_fast_solver_time:                   0.
% 7.94/1.51  prop_fast_solver_time:                  0.
% 7.94/1.51  prop_unsat_core_time:                   0.
% 7.94/1.51  
% 7.94/1.51  ------ QBF
% 7.94/1.51  
% 7.94/1.51  qbf_q_res:                              0
% 7.94/1.51  qbf_num_tautologies:                    0
% 7.94/1.51  qbf_prep_cycles:                        0
% 7.94/1.51  
% 7.94/1.51  ------ BMC1
% 7.94/1.51  
% 7.94/1.51  bmc1_current_bound:                     -1
% 7.94/1.51  bmc1_last_solved_bound:                 -1
% 7.94/1.51  bmc1_unsat_core_size:                   -1
% 7.94/1.51  bmc1_unsat_core_parents_size:           -1
% 7.94/1.51  bmc1_merge_next_fun:                    0
% 7.94/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.94/1.51  
% 7.94/1.51  ------ Instantiation
% 7.94/1.51  
% 7.94/1.51  inst_num_of_clauses:                    2213
% 7.94/1.51  inst_num_in_passive:                    860
% 7.94/1.51  inst_num_in_active:                     1181
% 7.94/1.51  inst_num_in_unprocessed:                171
% 7.94/1.51  inst_num_of_loops:                      1492
% 7.94/1.51  inst_num_of_learning_restarts:          0
% 7.94/1.51  inst_num_moves_active_passive:          305
% 7.94/1.51  inst_lit_activity:                      0
% 7.94/1.51  inst_lit_activity_moves:                0
% 7.94/1.51  inst_num_tautologies:                   0
% 7.94/1.51  inst_num_prop_implied:                  0
% 7.94/1.51  inst_num_existing_simplified:           0
% 7.94/1.51  inst_num_eq_res_simplified:             0
% 7.94/1.51  inst_num_child_elim:                    0
% 7.94/1.51  inst_num_of_dismatching_blockings:      5355
% 7.94/1.51  inst_num_of_non_proper_insts:           6501
% 7.94/1.51  inst_num_of_duplicates:                 0
% 7.94/1.51  inst_inst_num_from_inst_to_res:         0
% 7.94/1.51  inst_dismatching_checking_time:         0.
% 7.94/1.51  
% 7.94/1.51  ------ Resolution
% 7.94/1.51  
% 7.94/1.51  res_num_of_clauses:                     0
% 7.94/1.51  res_num_in_passive:                     0
% 7.94/1.51  res_num_in_active:                      0
% 7.94/1.51  res_num_of_loops:                       215
% 7.94/1.51  res_forward_subset_subsumed:            388
% 7.94/1.51  res_backward_subset_subsumed:           2
% 7.94/1.51  res_forward_subsumed:                   0
% 7.94/1.51  res_backward_subsumed:                  0
% 7.94/1.51  res_forward_subsumption_resolution:     6
% 7.94/1.51  res_backward_subsumption_resolution:    0
% 7.94/1.51  res_clause_to_clause_subsumption:       2718
% 7.94/1.51  res_orphan_elimination:                 0
% 7.94/1.51  res_tautology_del:                      608
% 7.94/1.51  res_num_eq_res_simplified:              0
% 7.94/1.51  res_num_sel_changes:                    0
% 7.94/1.51  res_moves_from_active_to_pass:          0
% 7.94/1.51  
% 7.94/1.51  ------ Superposition
% 7.94/1.51  
% 7.94/1.51  sup_time_total:                         0.
% 7.94/1.51  sup_time_generating:                    0.
% 7.94/1.51  sup_time_sim_full:                      0.
% 7.94/1.51  sup_time_sim_immed:                     0.
% 7.94/1.51  
% 7.94/1.51  sup_num_of_clauses:                     570
% 7.94/1.51  sup_num_in_active:                      284
% 7.94/1.51  sup_num_in_passive:                     286
% 7.94/1.51  sup_num_of_loops:                       298
% 7.94/1.51  sup_fw_superposition:                   599
% 7.94/1.51  sup_bw_superposition:                   376
% 7.94/1.51  sup_immediate_simplified:               307
% 7.94/1.51  sup_given_eliminated:                   0
% 7.94/1.51  comparisons_done:                       0
% 7.94/1.51  comparisons_avoided:                    11
% 7.94/1.51  
% 7.94/1.51  ------ Simplifications
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  sim_fw_subset_subsumed:                 90
% 7.94/1.51  sim_bw_subset_subsumed:                 28
% 7.94/1.51  sim_fw_subsumed:                        89
% 7.94/1.51  sim_bw_subsumed:                        16
% 7.94/1.51  sim_fw_subsumption_res:                 3
% 7.94/1.51  sim_bw_subsumption_res:                 0
% 7.94/1.51  sim_tautology_del:                      62
% 7.94/1.51  sim_eq_tautology_del:                   44
% 7.94/1.51  sim_eq_res_simp:                        0
% 7.94/1.51  sim_fw_demodulated:                     3
% 7.94/1.51  sim_bw_demodulated:                     8
% 7.94/1.51  sim_light_normalised:                   214
% 7.94/1.51  sim_joinable_taut:                      0
% 7.94/1.51  sim_joinable_simp:                      0
% 7.94/1.51  sim_ac_normalised:                      0
% 7.94/1.51  sim_smt_subsumption:                    0
% 7.94/1.51  
%------------------------------------------------------------------------------
