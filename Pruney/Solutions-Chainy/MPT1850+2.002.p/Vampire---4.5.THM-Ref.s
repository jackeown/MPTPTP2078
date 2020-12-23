%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 (1978 expanded)
%              Number of leaves         :   21 ( 623 expanded)
%              Depth                    :   18
%              Number of atoms          :  434 (9209 expanded)
%              Number of equality atoms :   39 (1620 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f548,plain,(
    $false ),
    inference(subsumption_resolution,[],[f547,f134])).

fof(f134,plain,(
    m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(u1_pre_topc(sK0))) ),
    inference(backward_demodulation,[],[f105,f127])).

fof(f127,plain,(
    u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f59,f62,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(f62,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ~ v1_tdlat_3(sK1)
    & v1_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tdlat_3(X1)
            & v1_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ~ v1_tdlat_3(X1)
        & v1_tdlat_3(sK0)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & l1_pre_topc(X1) )
   => ( ~ v1_tdlat_3(sK1)
      & v1_tdlat_3(sK0)
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v1_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v1_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v1_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v1_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f59,f92])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f68,f65,f65])).

fof(f65,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f547,plain,(
    ~ m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f546,f127])).

fof(f546,plain,(
    ~ m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f543,f418])).

fof(f418,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f291,f397,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f397,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f216,f60,f115,f263,f367,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f367,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f59,f216,f154,f144])).

fof(f144,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f143,f141])).

fof(f141,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f137,f60])).

fof(f137,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(superposition,[],[f82,f61])).

fof(f61,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f143,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | ~ v2_pre_topc(sK1)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f142,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f142,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f138,f60])).

fof(f138,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f101,f61])).

fof(f101,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f154,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f59,f104,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f104,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f59,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f263,plain,(
    m1_pre_topc(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f60,f128,f59,f232,f148,f168,f101])).

fof(f168,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(forward_demodulation,[],[f166,f61])).

fof(f166,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f60,f115,f74])).

fof(f148,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f59,f128,f82])).

fof(f232,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f59,f154,f73])).

fof(f128,plain,(
    v2_pre_topc(sK0) ),
    inference(unit_resulting_resolution,[],[f59,f62,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f115,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f60,f67])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f216,plain,(
    v2_pre_topc(sK1) ),
    inference(unit_resulting_resolution,[],[f148,f147])).

fof(f147,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f140,f60])).

fof(f140,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f70,f61])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_pre_topc)).

fof(f291,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f216,f60,f263,f115,f263,f85])).

fof(f543,plain,(
    ~ m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f367,f457,f198,f114])).

fof(f114,plain,(
    ! [X8,X7] :
      ( ~ v1_tops_2(X7,sK0)
      | ~ m1_subset_1(X7,k9_setfam_1(k9_setfam_1(u1_struct_0(X8))))
      | ~ m1_pre_topc(X8,sK0)
      | v1_tops_2(X7,X8) ) ),
    inference(subsumption_resolution,[],[f113,f110])).

fof(f110,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X4))))
      | ~ m1_pre_topc(X4,sK0)
      | m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f59,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) ) ),
    inference(definition_unfolding,[],[f75,f65,f65,f65,f65])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

fof(f113,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k9_setfam_1(k9_setfam_1(u1_struct_0(X8))))
      | ~ v1_tops_2(X7,sK0)
      | ~ m1_pre_topc(X8,sK0)
      | ~ m1_subset_1(X7,k9_setfam_1(k9_setfam_1(u1_struct_0(sK0))))
      | v1_tops_2(X7,X8) ) ),
    inference(resolution,[],[f59,f99])).

fof(f99,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | v1_tops_2(X3,X2) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f78,f65,f65,f65,f65])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

fof(f198,plain,(
    v1_tops_2(u1_pre_topc(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f134,f135])).

fof(f135,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k9_setfam_1(u1_pre_topc(sK0)))
      | v1_tops_2(X5,sK0) ) ),
    inference(subsumption_resolution,[],[f132,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f89,f65])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f132,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k9_setfam_1(u1_pre_topc(sK0)))
      | ~ r1_tarski(X5,u1_pre_topc(sK0))
      | v1_tops_2(X5,sK0) ) ),
    inference(backward_demodulation,[],[f111,f127])).

fof(f111,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,u1_pre_topc(sK0))
      | ~ m1_subset_1(X5,k9_setfam_1(k9_setfam_1(u1_struct_0(sK0))))
      | v1_tops_2(X5,sK0) ) ),
    inference(resolution,[],[f59,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0) ) ),
    inference(definition_unfolding,[],[f77,f65,f65])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(f457,plain,(
    ~ v1_tops_2(u1_pre_topc(sK0),sK1) ),
    inference(forward_demodulation,[],[f439,f127])).

fof(f439,plain,(
    ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK1) ),
    inference(backward_demodulation,[],[f337,f418])).

fof(f337,plain,(
    ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK1)),sK1) ),
    inference(subsumption_resolution,[],[f336,f213])).

fof(f213,plain,(
    ~ r1_tarski(k9_setfam_1(u1_struct_0(sK1)),u1_pre_topc(sK1)) ),
    inference(unit_resulting_resolution,[],[f136,f195,f88])).

fof(f195,plain,(
    r1_tarski(u1_pre_topc(sK1),k9_setfam_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f116,f98])).

fof(f116,plain,(
    m1_subset_1(u1_pre_topc(sK1),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f60,f92])).

fof(f136,plain,(
    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f60,f63,f72])).

fof(f72,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f63,plain,(
    ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f336,plain,
    ( r1_tarski(k9_setfam_1(u1_struct_0(sK1)),u1_pre_topc(sK1))
    | ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK1)),sK1) ),
    inference(forward_demodulation,[],[f335,f64])).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f335,plain,
    ( ~ v1_tops_2(k9_setfam_1(u1_struct_0(sK1)),sK1)
    | r1_tarski(k2_subset_1(k9_setfam_1(u1_struct_0(sK1))),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f331,f64])).

fof(f331,plain,
    ( ~ v1_tops_2(k2_subset_1(k9_setfam_1(u1_struct_0(sK1))),sK1)
    | r1_tarski(k2_subset_1(k9_setfam_1(u1_struct_0(sK1))),u1_pre_topc(sK1)) ),
    inference(resolution,[],[f123,f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f66,f65])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f123,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k9_setfam_1(k9_setfam_1(u1_struct_0(sK1))))
      | ~ v1_tops_2(X6,sK1)
      | r1_tarski(X6,u1_pre_topc(sK1)) ) ),
    inference(resolution,[],[f60,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | r1_tarski(X1,u1_pre_topc(X0)) ) ),
    inference(definition_unfolding,[],[f76,f65,f65])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:04:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (28299)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (28304)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (28322)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (28297)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (28314)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (28313)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (28305)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (28306)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (28296)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (28295)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (28295)Refutation not found, incomplete strategy% (28295)------------------------------
% 0.20/0.54  % (28295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (28295)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28295)Memory used [KB]: 1663
% 0.20/0.54  % (28295)Time elapsed: 0.120 s
% 0.20/0.54  % (28295)------------------------------
% 0.20/0.54  % (28295)------------------------------
% 0.20/0.54  % (28310)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (28317)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (28294)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.55  % (28303)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (28309)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (28319)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (28321)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (28300)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (28325)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (28311)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.56  % (28301)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.56  % (28315)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.56  % (28311)Refutation not found, incomplete strategy% (28311)------------------------------
% 0.20/0.56  % (28311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (28311)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (28311)Memory used [KB]: 10618
% 0.20/0.56  % (28311)Time elapsed: 0.145 s
% 0.20/0.56  % (28311)------------------------------
% 0.20/0.56  % (28311)------------------------------
% 0.20/0.56  % (28320)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  % (28316)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (28318)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.56  % (28302)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.56  % (28308)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.56  % (28324)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.56  % (28312)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.57  % (28298)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.57  % (28319)Refutation not found, incomplete strategy% (28319)------------------------------
% 0.20/0.57  % (28319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (28319)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (28319)Memory used [KB]: 10746
% 0.20/0.57  % (28319)Time elapsed: 0.145 s
% 0.20/0.57  % (28319)------------------------------
% 0.20/0.57  % (28319)------------------------------
% 0.20/0.57  % (28305)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f548,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(subsumption_resolution,[],[f547,f134])).
% 0.20/0.57  fof(f134,plain,(
% 0.20/0.57    m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(u1_pre_topc(sK0)))),
% 0.20/0.57    inference(backward_demodulation,[],[f105,f127])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f59,f62,f71])).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_tdlat_3(X0) | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ! [X0] : (((v1_tdlat_3(X0) | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))) & (u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0] : ((v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    v1_tdlat_3(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    (~v1_tdlat_3(sK1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f50,f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) => (~v1_tdlat_3(sK1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : ((~v1_tdlat_3(X1) & (v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,negated_conjecture,(
% 0.20/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 0.20/0.57    inference(negated_conjecture,[],[f21])).
% 0.20/0.57  fof(f21,conjecture,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    l1_pre_topc(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f51])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK0))))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f59,f92])).
% 0.20/0.57  fof(f92,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f68,f65,f65])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.57  fof(f547,plain,(
% 0.20/0.57    ~m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(u1_pre_topc(sK0)))),
% 0.20/0.57    inference(forward_demodulation,[],[f546,f127])).
% 0.20/0.57  fof(f546,plain,(
% 0.20/0.57    ~m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK0))))),
% 0.20/0.57    inference(forward_demodulation,[],[f543,f418])).
% 0.20/0.57  fof(f418,plain,(
% 0.20/0.57    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f291,f397,f88])).
% 0.20/0.57  fof(f88,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f57])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(flattening,[],[f56])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.57  fof(f397,plain,(
% 0.20/0.57    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f216,f60,f115,f263,f367,f85])).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f55])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,axiom,(
% 0.20/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.57  fof(f367,plain,(
% 0.20/0.57    m1_pre_topc(sK1,sK0)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f59,f216,f154,f144])).
% 0.20/0.57  fof(f144,plain,(
% 0.20/0.57    ( ! [X0] : (~v2_pre_topc(sK1) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f143,f141])).
% 0.20/0.57  fof(f141,plain,(
% 0.20/0.57    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1)),
% 0.20/0.57    inference(subsumption_resolution,[],[f137,f60])).
% 0.20/0.57  fof(f137,plain,(
% 0.20/0.57    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.20/0.57    inference(superposition,[],[f82,f61])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.20/0.57    inference(cnf_transformation,[],[f51])).
% 0.20/0.57  fof(f82,plain,(
% 0.20/0.57    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.20/0.57    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 0.20/0.57  fof(f143,plain,(
% 0.20/0.57    ( ! [X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~v2_pre_topc(sK1) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f142,f73])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.57  fof(f142,plain,(
% 0.20/0.57    ( ! [X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f138,f60])).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    ( ! [X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(superposition,[],[f101,f61])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    ( ! [X2,X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f80])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.20/0.57  fof(f154,plain,(
% 0.20/0.57    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f59,f104,f74])).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 0.20/0.57    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.20/0.57  fof(f104,plain,(
% 0.20/0.57    m1_pre_topc(sK0,sK0)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f59,f67])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.57  fof(f263,plain,(
% 0.20/0.57    m1_pre_topc(sK0,sK1)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f60,f128,f59,f232,f148,f168,f101])).
% 0.20/0.57  fof(f168,plain,(
% 0.20/0.57    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.20/0.57    inference(forward_demodulation,[],[f166,f61])).
% 0.20/0.57  fof(f166,plain,(
% 0.20/0.57    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f60,f115,f74])).
% 0.20/0.57  fof(f148,plain,(
% 0.20/0.57    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f59,f128,f82])).
% 0.20/0.57  fof(f232,plain,(
% 0.20/0.57    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f59,f154,f73])).
% 0.20/0.57  fof(f128,plain,(
% 0.20/0.57    v2_pre_topc(sK0)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f59,f62,f69])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.20/0.57  fof(f115,plain,(
% 0.20/0.57    m1_pre_topc(sK1,sK1)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f60,f67])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    l1_pre_topc(sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f51])).
% 0.20/0.57  fof(f216,plain,(
% 0.20/0.57    v2_pre_topc(sK1)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f148,f147])).
% 0.20/0.57  fof(f147,plain,(
% 0.20/0.57    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_pre_topc(sK1)),
% 0.20/0.57    inference(subsumption_resolution,[],[f140,f60])).
% 0.20/0.57  fof(f140,plain,(
% 0.20/0.57    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_pre_topc(sK1) | ~l1_pre_topc(sK1)),
% 0.20/0.57    inference(superposition,[],[f70,f61])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    ( ! [X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0] : (v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0] : ((v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => v2_pre_topc(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_pre_topc)).
% 0.20/0.57  fof(f291,plain,(
% 0.20/0.57    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f216,f60,f263,f115,f263,f85])).
% 0.20/0.57  fof(f543,plain,(
% 0.20/0.57    ~m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1))))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f367,f457,f198,f114])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    ( ! [X8,X7] : (~v1_tops_2(X7,sK0) | ~m1_subset_1(X7,k9_setfam_1(k9_setfam_1(u1_struct_0(X8)))) | ~m1_pre_topc(X8,sK0) | v1_tops_2(X7,X8)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f113,f110])).
% 0.20/0.57  fof(f110,plain,(
% 0.20/0.57    ( ! [X4,X3] : (~m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X4)))) | ~m1_pre_topc(X4,sK0) | m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(sK0))))) )),
% 0.20/0.57    inference(resolution,[],[f59,f93])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0) | m1_subset_1(X2,k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f75,f65,f65,f65,f65])).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).
% 0.20/0.57  fof(f113,plain,(
% 0.20/0.57    ( ! [X8,X7] : (~m1_subset_1(X7,k9_setfam_1(k9_setfam_1(u1_struct_0(X8)))) | ~v1_tops_2(X7,sK0) | ~m1_pre_topc(X8,sK0) | ~m1_subset_1(X7,k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) | v1_tops_2(X7,X8)) )),
% 0.20/0.57    inference(resolution,[],[f59,f99])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) | v1_tops_2(X3,X2)) )),
% 0.20/0.57    inference(equality_resolution,[],[f96])).
% 0.20/0.57  fof(f96,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k9_setfam_1(k9_setfam_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f78,f65,f65,f65,f65])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).
% 0.20/0.57  fof(f198,plain,(
% 0.20/0.57    v1_tops_2(u1_pre_topc(sK0),sK0)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f134,f135])).
% 0.20/0.57  fof(f135,plain,(
% 0.20/0.57    ( ! [X5] : (~m1_subset_1(X5,k9_setfam_1(u1_pre_topc(sK0))) | v1_tops_2(X5,sK0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f132,f98])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k9_setfam_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f89,f65])).
% 0.20/0.57  fof(f89,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f58])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.57  fof(f132,plain,(
% 0.20/0.57    ( ! [X5] : (~m1_subset_1(X5,k9_setfam_1(u1_pre_topc(sK0))) | ~r1_tarski(X5,u1_pre_topc(sK0)) | v1_tops_2(X5,sK0)) )),
% 0.20/0.57    inference(backward_demodulation,[],[f111,f127])).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    ( ! [X5] : (~r1_tarski(X5,u1_pre_topc(sK0)) | ~m1_subset_1(X5,k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) | v1_tops_2(X5,sK0)) )),
% 0.20/0.57    inference(resolution,[],[f59,f94])).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f77,f65,f65])).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).
% 0.20/0.57  fof(f457,plain,(
% 0.20/0.57    ~v1_tops_2(u1_pre_topc(sK0),sK1)),
% 0.20/0.57    inference(forward_demodulation,[],[f439,f127])).
% 0.20/0.57  fof(f439,plain,(
% 0.20/0.57    ~v1_tops_2(k9_setfam_1(u1_struct_0(sK0)),sK1)),
% 0.20/0.57    inference(backward_demodulation,[],[f337,f418])).
% 0.20/0.57  fof(f337,plain,(
% 0.20/0.57    ~v1_tops_2(k9_setfam_1(u1_struct_0(sK1)),sK1)),
% 0.20/0.57    inference(subsumption_resolution,[],[f336,f213])).
% 0.20/0.57  fof(f213,plain,(
% 0.20/0.57    ~r1_tarski(k9_setfam_1(u1_struct_0(sK1)),u1_pre_topc(sK1))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f136,f195,f88])).
% 0.20/0.57  fof(f195,plain,(
% 0.20/0.57    r1_tarski(u1_pre_topc(sK1),k9_setfam_1(u1_struct_0(sK1)))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f116,f98])).
% 0.20/0.57  fof(f116,plain,(
% 0.20/0.57    m1_subset_1(u1_pre_topc(sK1),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1))))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f60,f92])).
% 0.20/0.57  fof(f136,plain,(
% 0.20/0.57    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f60,f63,f72])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X0] : (u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) | v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f52])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    ~v1_tdlat_3(sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f51])).
% 0.20/0.57  fof(f336,plain,(
% 0.20/0.57    r1_tarski(k9_setfam_1(u1_struct_0(sK1)),u1_pre_topc(sK1)) | ~v1_tops_2(k9_setfam_1(u1_struct_0(sK1)),sK1)),
% 0.20/0.57    inference(forward_demodulation,[],[f335,f64])).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.57  fof(f335,plain,(
% 0.20/0.57    ~v1_tops_2(k9_setfam_1(u1_struct_0(sK1)),sK1) | r1_tarski(k2_subset_1(k9_setfam_1(u1_struct_0(sK1))),u1_pre_topc(sK1))),
% 0.20/0.57    inference(forward_demodulation,[],[f331,f64])).
% 0.20/0.57  fof(f331,plain,(
% 0.20/0.57    ~v1_tops_2(k2_subset_1(k9_setfam_1(u1_struct_0(sK1))),sK1) | r1_tarski(k2_subset_1(k9_setfam_1(u1_struct_0(sK1))),u1_pre_topc(sK1))),
% 0.20/0.57    inference(resolution,[],[f123,f91])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f66,f65])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    ( ! [X6] : (~m1_subset_1(X6,k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) | ~v1_tops_2(X6,sK1) | r1_tarski(X6,u1_pre_topc(sK1))) )),
% 0.20/0.57    inference(resolution,[],[f60,f95])).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(u1_struct_0(X0)))) | r1_tarski(X1,u1_pre_topc(X0))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f76,f65,f65])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f53])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (28305)------------------------------
% 0.20/0.57  % (28305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (28305)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (28305)Memory used [KB]: 6396
% 0.20/0.57  % (28305)Time elapsed: 0.155 s
% 0.20/0.57  % (28305)------------------------------
% 0.20/0.57  % (28305)------------------------------
% 0.20/0.57  % (28290)Success in time 0.207 s
%------------------------------------------------------------------------------
