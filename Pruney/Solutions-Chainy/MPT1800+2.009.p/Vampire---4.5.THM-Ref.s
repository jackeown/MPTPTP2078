%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 (5496 expanded)
%              Number of leaves         :   16 (1521 expanded)
%              Depth                    :   25
%              Number of atoms          :  506 (48404 expanded)
%              Number of equality atoms :  106 (8324 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f535,plain,(
    $false ),
    inference(global_subsumption,[],[f254,f515,f534])).

fof(f534,plain,(
    ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(backward_demodulation,[],[f532,f531])).

fof(f531,plain,(
    u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f49,f51,f489,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f489,plain,(
    ~ v1_tsep_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f467])).

fof(f467,plain,
    ( k8_tmap_1(sK0,sK0) != k8_tmap_1(sK0,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f210,f442])).

fof(f442,plain,(
    k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f441])).

fof(f441,plain,
    ( k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0)
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0) ),
    inference(forward_demodulation,[],[f435,f205])).

fof(f205,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f136,f201])).

fof(f201,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK0)) ),
    inference(backward_demodulation,[],[f192,f199])).

fof(f199,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f103,f198,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f198,plain,(
    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f49,f103,f197,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f197,plain,(
    v3_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f193,f102])).

fof(f102,plain,(
    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f82,f100])).

fof(f100,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f87,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f87,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f82,plain,(
    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f78,f49])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f48,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(f193,plain,(
    v3_pre_topc(k1_tops_1(sK0,u1_struct_0(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f48,f49,f103,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f103,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f49,f88,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f88,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f49,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f38,plain,
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
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1)
            | ~ m1_pre_topc(X1,sK0)
            | ~ v1_tsep_1(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1)
            | ( m1_pre_topc(X1,sK0)
              & v1_tsep_1(X1,sK0) ) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1)
          | ~ m1_pre_topc(X1,sK0)
          | ~ v1_tsep_1(X1,sK0) )
        & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1)
          | ( m1_pre_topc(X1,sK0)
            & v1_tsep_1(X1,sK0) ) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_tsep_1(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
        | ( m1_pre_topc(sK1,sK0)
          & v1_tsep_1(sK1,sK0) ) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f192,plain,(
    u1_pre_topc(k8_tmap_1(sK0,sK0)) = k5_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f47,f88,f103,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

fof(f136,plain,(
    k8_tmap_1(sK0,sK0) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f135,f104])).

fof(f104,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f47,f88,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f135,plain,(
    k8_tmap_1(sK0,sK0) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK0)),u1_pre_topc(k8_tmap_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f134,f107])).

fof(f107,plain,(
    l1_pre_topc(k8_tmap_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f88,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f134,plain,
    ( k8_tmap_1(sK0,sK0) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK0)),u1_pre_topc(k8_tmap_1(sK0,sK0)))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK0)) ),
    inference(resolution,[],[f105,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

% (17905)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f105,plain,(
    v1_pre_topc(k8_tmap_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f88,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f435,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0) ),
    inference(superposition,[],[f110,f309])).

fof(f309,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0) ),
    inference(resolution,[],[f308,f207])).

fof(f207,plain,
    ( v1_tsep_1(sK1,sK0)
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f52,f205])).

fof(f52,plain,
    ( v1_tsep_1(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f308,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f306,f165])).

fof(f165,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f164,f49])).

fof(f164,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f163,f51])).

fof(f163,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f95,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f49,f51,f59])).

fof(f306,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f267,f248])).

fof(f248,plain,
    ( r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(resolution,[],[f90,f95])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | r2_hidden(X0,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f49,f64])).

fof(f267,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f263,f160])).

fof(f160,plain,(
    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f50,f51,f95,f76])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f263,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(resolution,[],[f86,f95])).

fof(f86,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X2) ) ),
    inference(subsumption_resolution,[],[f85,f47])).

fof(f85,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_pre_topc(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f49])).

fof(f80,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_pre_topc(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f48,f66])).

fof(f110,plain,(
    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f109,f96])).

fof(f96,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f50,f51,f68])).

fof(f109,plain,(
    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f108,f99])).

fof(f99,plain,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f51,f73])).

fof(f108,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f97,f58])).

fof(f97,plain,(
    v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f48,f49,f51,f71])).

fof(f210,plain,
    ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f209,f51])).

fof(f209,plain,
    ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f54,f205])).

fof(f54,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

% (17896)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f532,plain,(
    ~ v3_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f49,f51,f489,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f515,plain,(
    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f468,f201])).

fof(f468,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK0))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f246,f442])).

fof(f246,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f245,f47])).

fof(f245,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f244,f48])).

fof(f244,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f243,f49])).

fof(f243,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f242,f95])).

fof(f242,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f67,f160])).

fof(f67,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f254,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(resolution,[],[f91,f95])).

fof(f91,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,u1_pre_topc(sK0))
      | v3_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f49,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.35  % Computer   : n025.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 18:58:21 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.21/0.44  % (17910)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (17897)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.46  % (17902)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (17904)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (17910)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f535,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(global_subsumption,[],[f254,f515,f534])).
% 0.21/0.47  fof(f534,plain,(
% 0.21/0.47    ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f532,f531])).
% 0.21/0.47  fof(f531,plain,(
% 0.21/0.47    u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f49,f51,f489,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(rectify,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).
% 0.21/0.47  fof(f489,plain,(
% 0.21/0.47    ~v1_tsep_1(sK1,sK0)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f467])).
% 0.21/0.47  fof(f467,plain,(
% 0.21/0.47    k8_tmap_1(sK0,sK0) != k8_tmap_1(sK0,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f210,f442])).
% 0.21/0.47  fof(f442,plain,(
% 0.21/0.47    k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f441])).
% 0.21/0.47  fof(f441,plain,(
% 0.21/0.47    k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0)),
% 0.21/0.47    inference(forward_demodulation,[],[f435,f205])).
% 0.21/0.47  fof(f205,plain,(
% 0.21/0.47    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f136,f201])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK0))),
% 0.21/0.47    inference(backward_demodulation,[],[f192,f199])).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f47,f48,f49,f103,f198,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f49,f103,f197,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.47  fof(f197,plain,(
% 0.21/0.47    v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.21/0.47    inference(forward_demodulation,[],[f193,f102])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.21/0.47    inference(backward_demodulation,[],[f82,f100])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f87,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    l1_struct_0(sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f49,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f78,f49])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.21/0.48    inference(resolution,[],[f48,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    v3_pre_topc(k1_tops_1(sK0,u1_struct_0(sK0)),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f48,f49,f103,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f49,f88,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    m1_pre_topc(sK0,sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f49,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f13])).
% 0.21/0.48  fof(f13,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    u1_pre_topc(k8_tmap_1(sK0,sK0)) = k5_tmap_1(sK0,u1_struct_0(sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f47,f48,f49,f47,f88,f103,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    k8_tmap_1(sK0,sK0) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK0)))),
% 0.21/0.48    inference(forward_demodulation,[],[f135,f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f47,f48,f49,f47,f88,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    k8_tmap_1(sK0,sK0) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK0)),u1_pre_topc(k8_tmap_1(sK0,sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    l1_pre_topc(k8_tmap_1(sK0,sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f47,f48,f49,f88,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    k8_tmap_1(sK0,sK0) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK0)),u1_pre_topc(k8_tmap_1(sK0,sK0))) | ~l1_pre_topc(k8_tmap_1(sK0,sK0))),
% 0.21/0.48    inference(resolution,[],[f105,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  % (17905)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    v1_pre_topc(k8_tmap_1(sK0,sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f47,f48,f49,f88,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f435,plain,(
% 0.21/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0)),
% 0.21/0.48    inference(superposition,[],[f110,f309])).
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0)),
% 0.21/0.48    inference(resolution,[],[f308,f207])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    v1_tsep_1(sK1,sK0) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0)),
% 0.21/0.48    inference(backward_demodulation,[],[f52,f205])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    v1_tsep_1(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    ~v1_tsep_1(sK1,sK0) | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f306,f165])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f164,f49])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f163,f51])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f95,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f44])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f49,f51,f59])).
% 0.21/0.48  fof(f306,plain,(
% 0.21/0.48    ~v3_pre_topc(u1_struct_0(sK1),sK0) | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f267,f248])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.48    inference(resolution,[],[f90,f95])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | r2_hidden(X0,u1_pre_topc(sK0))) )),
% 0.21/0.48    inference(resolution,[],[f49,f64])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(forward_demodulation,[],[f263,f160])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f47,f48,f49,f50,f51,f95,f76])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ~v2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.48    inference(resolution,[],[f86,f95])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f47])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(X2,u1_pre_topc(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X2) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f80,f49])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(X2,u1_pre_topc(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X2) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f48,f66])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 0.21/0.48    inference(forward_demodulation,[],[f109,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f47,f48,f49,f50,f51,f68])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f108,f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f47,f48,f49,f51,f73])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f97,f58])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f47,f48,f49,f51,f71])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f209,f51])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.48    inference(backward_demodulation,[],[f54,f205])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  % (17896)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f532,plain,(
% 0.21/0.48    ~v3_pre_topc(sK2(sK0,sK1),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f49,f51,f489,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(sK2(X0,X1),X0) | ~m1_pre_topc(X1,X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f44])).
% 0.21/0.48  fof(f515,plain,(
% 0.21/0.48    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f468,f201])).
% 0.21/0.48  fof(f468,plain,(
% 0.21/0.48    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK0)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.48    inference(backward_demodulation,[],[f246,f442])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f245,f47])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f244,f48])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f243,f49])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f242,f95])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(superposition,[],[f67,f160])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f46])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.48    inference(resolution,[],[f91,f95])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,u1_pre_topc(sK0)) | v3_pre_topc(X1,sK0)) )),
% 0.21/0.48    inference(resolution,[],[f49,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f45])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17910)------------------------------
% 0.21/0.48  % (17910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17910)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17910)Memory used [KB]: 6396
% 0.21/0.48  % (17910)Time elapsed: 0.040 s
% 0.21/0.48  % (17910)------------------------------
% 0.21/0.48  % (17910)------------------------------
% 0.21/0.48  % (17896)Refutation not found, incomplete strategy% (17896)------------------------------
% 0.21/0.48  % (17896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17896)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (17896)Memory used [KB]: 10618
% 0.21/0.48  % (17896)Time elapsed: 0.072 s
% 0.21/0.48  % (17896)------------------------------
% 0.21/0.48  % (17896)------------------------------
% 0.21/0.48  % (17894)Success in time 0.124 s
%------------------------------------------------------------------------------
