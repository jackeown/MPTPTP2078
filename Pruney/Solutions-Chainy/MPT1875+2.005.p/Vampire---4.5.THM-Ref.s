%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 294 expanded)
%              Number of leaves         :   25 (  85 expanded)
%              Depth                    :   18
%              Number of atoms          :  538 (1283 expanded)
%              Number of equality atoms :   36 (  71 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1292,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f1154,f112,f1287,f110])).

fof(f110,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f110_D])).

fof(f110_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f1287,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f1286,f70])).

fof(f70,plain,(
    v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ v2_tex_2(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v1_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v1_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ~ v2_tex_2(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f1286,plain,
    ( ~ v1_tdlat_3(sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f1285,f73])).

fof(f73,plain,(
    ~ v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f1285,plain,
    ( v2_tex_2(sK2,sK1)
    | ~ v1_tdlat_3(sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f1284,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f1284,plain,
    ( v2_struct_0(sK1)
    | v2_tex_2(sK2,sK1)
    | ~ v1_tdlat_3(sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f1261,f71])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f1261,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v2_tex_2(sK2,sK1)
    | ~ v1_tdlat_3(sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f573,f170])).

fof(f170,plain,
    ( sP0(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f169,f68])).

fof(f169,plain,
    ( sP0(sK2,sK1)
    | v1_xboole_0(sK2)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f163,f71])).

fof(f163,plain,
    ( sP0(sK2,sK1)
    | v1_xboole_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f87,f72])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f35,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f573,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_tex_2(X0,X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(duplicate_literal_removal,[],[f572])).

fof(f572,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X0,X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP0(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f339,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK4(X0,X1))
      | ~ l1_pre_topc(X1)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f154,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK4(X0,X1),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( u1_struct_0(sK4(X0,X1)) = X0
        & m1_pre_topc(sK4(X0,X1),X1)
        & ~ v2_struct_0(sK4(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK4(X0,X1)) = X0
        & m1_pre_topc(sK4(X0,X1),X1)
        & ~ v2_struct_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f90,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f339,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(sK4(X0,X1))
      | v2_tex_2(X0,X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(sK4(X0,X1))
      | v2_tex_2(X0,X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP0(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f207,f85])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(sK4(X0,X1),X2)
      | ~ v1_tdlat_3(sK4(X0,X1))
      | v2_tex_2(X0,X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f204,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X0,X2)
      | ~ v1_tdlat_3(sK4(X0,X1))
      | ~ m1_pre_topc(sK4(X0,X1),X2)
      | v2_struct_0(sK4(X0,X1))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ sP0(X0,X1) ) ),
    inference(superposition,[],[f181,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK4(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f181,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f106,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f106,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f112,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f75,f74])).

fof(f74,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f1154,plain,(
    ~ sP7(sK2) ),
    inference(subsumption_resolution,[],[f1153,f68])).

fof(f1153,plain,
    ( ~ sP7(sK2)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f1152,f71])).

fof(f1152,plain,
    ( ~ sP7(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f1148,f70])).

fof(f1148,plain,
    ( ~ sP7(sK2)
    | ~ v1_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f1104,f172])).

fof(f172,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(X0),X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f104,f112])).

fof(f104,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(X0),X0)
      | ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_tdlat_3(X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_tdlat_3(X0) )
            & ( v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) ) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

fof(f1104,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK1)
    | ~ sP7(sK2) ),
    inference(subsumption_resolution,[],[f1095,f73])).

fof(f1095,plain,
    ( v2_tex_2(sK2,sK1)
    | ~ v2_tex_2(u1_struct_0(sK1),sK1)
    | ~ sP7(sK2) ),
    inference(superposition,[],[f445,f1013])).

fof(f1013,plain,(
    ! [X8,X7] :
      ( k3_xboole_0(X8,X7) = X7
      | ~ sP7(X7) ) ),
    inference(duplicate_literal_removal,[],[f1000])).

fof(f1000,plain,(
    ! [X8,X7] :
      ( ~ sP7(X7)
      | k3_xboole_0(X8,X7) = X7
      | ~ sP7(X7) ) ),
    inference(resolution,[],[f994,f130])).

fof(f130,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ sP7(X2) ) ),
    inference(resolution,[],[f94,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ sP7(X0) ) ),
    inference(resolution,[],[f96,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f103,f110_D])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f64,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f994,plain,(
    ! [X4,X3] :
      ( r1_tarski(k3_xboole_0(X4,X3),X3)
      | ~ sP7(X3) ) ),
    inference(superposition,[],[f948,f228])).

fof(f228,plain,(
    ! [X5] :
      ( sK5(k1_zfmisc_1(X5)) = X5
      | ~ sP7(X5) ) ),
    inference(resolution,[],[f130,f114])).

fof(f114,plain,(
    ! [X0] : r1_tarski(sK5(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f98,f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f7,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f948,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X2,sK5(k1_zfmisc_1(X3))),X3) ),
    inference(resolution,[],[f365,f112])).

fof(f365,plain,(
    ! [X24,X23,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(sK5(k1_zfmisc_1(X23))))
      | r1_tarski(k3_xboole_0(X24,X22),X23) ) ),
    inference(resolution,[],[f246,f137])).

fof(f137,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,sK5(k1_zfmisc_1(X7)))
      | r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f102,f114])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f246,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f245])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f143,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f143,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k9_subset_1(X4,X5,X3),X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f100,f98])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f445,plain,
    ( v2_tex_2(k3_xboole_0(u1_struct_0(sK1),sK2),sK1)
    | ~ v2_tex_2(u1_struct_0(sK1),sK1) ),
    inference(resolution,[],[f357,f112])).

fof(f357,plain,(
    ! [X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_tex_2(k3_xboole_0(X16,sK2),sK1)
      | ~ v2_tex_2(X16,sK1) ) ),
    inference(subsumption_resolution,[],[f349,f71])).

fof(f349,plain,(
    ! [X16] :
      ( ~ v2_tex_2(X16,sK1)
      | v2_tex_2(k3_xboole_0(X16,sK2),sK1)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f222,f72])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k3_xboole_0(X1,X2),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f78,f101])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:36:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (21188)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (21197)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (21180)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (21178)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (21184)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (21184)Refutation not found, incomplete strategy% (21184)------------------------------
% 0.21/0.52  % (21184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21184)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21184)Memory used [KB]: 10618
% 0.21/0.52  % (21184)Time elapsed: 0.109 s
% 0.21/0.52  % (21184)------------------------------
% 0.21/0.52  % (21184)------------------------------
% 0.21/0.52  % (21185)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (21186)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (21204)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (21179)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (21174)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (21202)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (21199)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (21193)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (21175)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (21198)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (21176)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (21173)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (21177)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (21173)Refutation not found, incomplete strategy% (21173)------------------------------
% 0.21/0.54  % (21173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21173)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21173)Memory used [KB]: 1663
% 0.21/0.54  % (21173)Time elapsed: 0.125 s
% 0.21/0.54  % (21173)------------------------------
% 0.21/0.54  % (21173)------------------------------
% 0.21/0.54  % (21182)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (21196)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (21189)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (21182)Refutation not found, incomplete strategy% (21182)------------------------------
% 0.21/0.54  % (21182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21182)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21182)Memory used [KB]: 10618
% 0.21/0.54  % (21182)Time elapsed: 0.138 s
% 0.21/0.54  % (21182)------------------------------
% 0.21/0.54  % (21182)------------------------------
% 0.21/0.54  % (21200)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (21190)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (21190)Refutation not found, incomplete strategy% (21190)------------------------------
% 0.21/0.55  % (21190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21190)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21190)Memory used [KB]: 10618
% 0.21/0.55  % (21190)Time elapsed: 0.138 s
% 0.21/0.55  % (21190)------------------------------
% 0.21/0.55  % (21190)------------------------------
% 0.21/0.55  % (21187)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (21181)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (21192)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (21203)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (21183)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (21183)Refutation not found, incomplete strategy% (21183)------------------------------
% 0.21/0.56  % (21183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21183)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21183)Memory used [KB]: 10618
% 0.21/0.56  % (21183)Time elapsed: 0.148 s
% 0.21/0.56  % (21183)------------------------------
% 0.21/0.56  % (21183)------------------------------
% 0.21/0.56  % (21194)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (21195)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.60  % (21204)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 1.81/0.61  % SZS output start Proof for theBenchmark
% 1.81/0.61  fof(f1292,plain,(
% 1.81/0.61    $false),
% 1.81/0.61    inference(unit_resulting_resolution,[],[f1154,f112,f1287,f110])).
% 1.81/0.61  fof(f110,plain,(
% 1.81/0.61    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP7(X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f110_D])).
% 1.81/0.61  fof(f110_D,plain,(
% 1.81/0.61    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP7(X1)) )),
% 1.81/0.61    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.81/0.61  fof(f1287,plain,(
% 1.81/0.61    v1_xboole_0(sK2)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1286,f70])).
% 1.81/0.61  fof(f70,plain,(
% 1.81/0.61    v1_tdlat_3(sK1)),
% 1.81/0.61    inference(cnf_transformation,[],[f50])).
% 1.81/0.61  fof(f50,plain,(
% 1.81/0.61    (~v2_tex_2(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f49,f48])).
% 1.81/0.61  fof(f48,plain,(
% 1.81/0.61    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f49,plain,(
% 1.81/0.61    ? [X1] : (~v2_tex_2(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) => (~v2_tex_2(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f25,plain,(
% 1.81/0.61    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.81/0.61    inference(flattening,[],[f24])).
% 1.81/0.61  fof(f24,plain,(
% 1.81/0.61    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f20])).
% 1.81/0.61  fof(f20,negated_conjecture,(
% 1.81/0.61    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.81/0.61    inference(negated_conjecture,[],[f19])).
% 1.81/0.61  fof(f19,conjecture,(
% 1.81/0.61    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 1.81/0.61  fof(f1286,plain,(
% 1.81/0.61    ~v1_tdlat_3(sK1) | v1_xboole_0(sK2)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1285,f73])).
% 1.81/0.61  fof(f73,plain,(
% 1.81/0.61    ~v2_tex_2(sK2,sK1)),
% 1.81/0.61    inference(cnf_transformation,[],[f50])).
% 1.81/0.61  fof(f1285,plain,(
% 1.81/0.61    v2_tex_2(sK2,sK1) | ~v1_tdlat_3(sK1) | v1_xboole_0(sK2)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1284,f68])).
% 1.81/0.61  fof(f68,plain,(
% 1.81/0.61    ~v2_struct_0(sK1)),
% 1.81/0.61    inference(cnf_transformation,[],[f50])).
% 1.81/0.61  fof(f1284,plain,(
% 1.81/0.61    v2_struct_0(sK1) | v2_tex_2(sK2,sK1) | ~v1_tdlat_3(sK1) | v1_xboole_0(sK2)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1261,f71])).
% 1.81/0.61  fof(f71,plain,(
% 1.81/0.61    l1_pre_topc(sK1)),
% 1.81/0.61    inference(cnf_transformation,[],[f50])).
% 1.81/0.61  fof(f1261,plain,(
% 1.81/0.61    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | v2_tex_2(sK2,sK1) | ~v1_tdlat_3(sK1) | v1_xboole_0(sK2)),
% 1.81/0.61    inference(resolution,[],[f573,f170])).
% 1.81/0.61  fof(f170,plain,(
% 1.81/0.61    sP0(sK2,sK1) | v1_xboole_0(sK2)),
% 1.81/0.61    inference(subsumption_resolution,[],[f169,f68])).
% 1.81/0.61  fof(f169,plain,(
% 1.81/0.61    sP0(sK2,sK1) | v1_xboole_0(sK2) | v2_struct_0(sK1)),
% 1.81/0.61    inference(subsumption_resolution,[],[f163,f71])).
% 1.81/0.61  fof(f163,plain,(
% 1.81/0.61    sP0(sK2,sK1) | v1_xboole_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.81/0.61    inference(resolution,[],[f87,f72])).
% 1.81/0.61  fof(f72,plain,(
% 1.81/0.61    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.81/0.61    inference(cnf_transformation,[],[f50])).
% 1.81/0.61  fof(f87,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP0(X1,X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f47])).
% 1.81/0.61  fof(f47,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (sP0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.81/0.61    inference(definition_folding,[],[f35,f46])).
% 1.81/0.61  fof(f46,plain,(
% 1.81/0.61    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~sP0(X1,X0))),
% 1.81/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.81/0.61  fof(f35,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.81/0.61    inference(flattening,[],[f34])).
% 1.81/0.61  fof(f34,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f21])).
% 1.81/0.61  fof(f21,plain,(
% 1.81/0.61    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 1.81/0.61    inference(pure_predicate_removal,[],[f15])).
% 1.81/0.61  fof(f15,axiom,(
% 1.81/0.61    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 1.81/0.61  fof(f573,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~sP0(X0,X1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | v2_tex_2(X0,X1) | ~v1_tdlat_3(X1)) )),
% 1.81/0.61    inference(duplicate_literal_removal,[],[f572])).
% 1.81/0.61  fof(f572,plain,(
% 1.81/0.61    ( ! [X0,X1] : (v2_tex_2(X0,X1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~sP0(X0,X1) | ~l1_pre_topc(X1) | ~v1_tdlat_3(X1) | v2_struct_0(X1) | ~sP0(X0,X1)) )),
% 1.81/0.61    inference(resolution,[],[f339,f155])).
% 1.81/0.61  fof(f155,plain,(
% 1.81/0.61    ( ! [X0,X1] : (v1_tdlat_3(sK4(X0,X1)) | ~l1_pre_topc(X1) | ~v1_tdlat_3(X1) | v2_struct_0(X1) | ~sP0(X0,X1)) )),
% 1.81/0.61    inference(resolution,[],[f154,f85])).
% 1.81/0.61  fof(f85,plain,(
% 1.81/0.61    ( ! [X0,X1] : (m1_pre_topc(sK4(X0,X1),X1) | ~sP0(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f57])).
% 1.81/0.61  fof(f57,plain,(
% 1.81/0.61    ! [X0,X1] : ((u1_struct_0(sK4(X0,X1)) = X0 & m1_pre_topc(sK4(X0,X1),X1) & ~v2_struct_0(sK4(X0,X1))) | ~sP0(X0,X1))),
% 1.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).
% 1.81/0.61  fof(f56,plain,(
% 1.81/0.61    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (u1_struct_0(sK4(X0,X1)) = X0 & m1_pre_topc(sK4(X0,X1),X1) & ~v2_struct_0(sK4(X0,X1))))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f55,plain,(
% 1.81/0.61    ! [X0,X1] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) | ~sP0(X0,X1))),
% 1.81/0.61    inference(rectify,[],[f54])).
% 1.81/0.61  fof(f54,plain,(
% 1.81/0.61    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~sP0(X1,X0))),
% 1.81/0.61    inference(nnf_transformation,[],[f46])).
% 1.81/0.61  fof(f154,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_tdlat_3(X1) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.81/0.61    inference(subsumption_resolution,[],[f90,f76])).
% 1.81/0.61  fof(f76,plain,(
% 1.81/0.61    ( ! [X0] : (~v1_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f27])).
% 1.81/0.61  fof(f27,plain,(
% 1.81/0.61    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.81/0.61    inference(flattening,[],[f26])).
% 1.81/0.61  fof(f26,plain,(
% 1.81/0.61    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.81/0.61    inference(ennf_transformation,[],[f13])).
% 1.81/0.61  fof(f13,axiom,(
% 1.81/0.61    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 1.81/0.61  fof(f90,plain,(
% 1.81/0.61    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f39])).
% 1.81/0.61  fof(f39,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.81/0.61    inference(flattening,[],[f38])).
% 1.81/0.61  fof(f38,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f23])).
% 1.81/0.61  fof(f23,plain,(
% 1.81/0.61    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 1.81/0.61    inference(pure_predicate_removal,[],[f22])).
% 1.81/0.61  fof(f22,plain,(
% 1.81/0.61    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 1.81/0.61    inference(pure_predicate_removal,[],[f14])).
% 1.81/0.61  fof(f14,axiom,(
% 1.81/0.61    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 1.81/0.61  fof(f339,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~v1_tdlat_3(sK4(X0,X1)) | v2_tex_2(X0,X1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~sP0(X0,X1)) )),
% 1.81/0.61    inference(duplicate_literal_removal,[],[f338])).
% 1.81/0.61  fof(f338,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~v1_tdlat_3(sK4(X0,X1)) | v2_tex_2(X0,X1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~sP0(X0,X1) | ~sP0(X0,X1)) )),
% 1.81/0.61    inference(resolution,[],[f207,f85])).
% 1.81/0.61  fof(f207,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (~m1_pre_topc(sK4(X0,X1),X2) | ~v1_tdlat_3(sK4(X0,X1)) | v2_tex_2(X0,X2) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP0(X0,X1)) )),
% 1.81/0.61    inference(subsumption_resolution,[],[f204,f84])).
% 1.81/0.61  fof(f84,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~v2_struct_0(sK4(X0,X1)) | ~sP0(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f57])).
% 1.81/0.61  fof(f204,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (v2_tex_2(X0,X2) | ~v1_tdlat_3(sK4(X0,X1)) | ~m1_pre_topc(sK4(X0,X1),X2) | v2_struct_0(sK4(X0,X1)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP0(X0,X1)) )),
% 1.81/0.61    inference(superposition,[],[f181,f86])).
% 1.81/0.61  fof(f86,plain,(
% 1.81/0.61    ( ! [X0,X1] : (u1_struct_0(sK4(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f57])).
% 1.81/0.61  fof(f181,plain,(
% 1.81/0.61    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.61    inference(subsumption_resolution,[],[f106,f77])).
% 1.81/0.61  fof(f77,plain,(
% 1.81/0.61    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f28])).
% 1.81/0.61  fof(f28,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.81/0.61    inference(ennf_transformation,[],[f12])).
% 1.81/0.61  fof(f12,axiom,(
% 1.81/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.81/0.61  fof(f106,plain,(
% 1.81/0.61    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.61    inference(equality_resolution,[],[f89])).
% 1.81/0.61  fof(f89,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f58])).
% 1.81/0.61  fof(f58,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.81/0.61    inference(nnf_transformation,[],[f37])).
% 1.81/0.61  fof(f37,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.81/0.61    inference(flattening,[],[f36])).
% 1.81/0.61  fof(f36,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f16])).
% 1.81/0.61  fof(f16,axiom,(
% 1.81/0.61    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 1.81/0.61  fof(f112,plain,(
% 1.81/0.61    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.81/0.61    inference(forward_demodulation,[],[f75,f74])).
% 1.81/0.61  fof(f74,plain,(
% 1.81/0.61    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.81/0.61    inference(cnf_transformation,[],[f4])).
% 1.81/0.61  fof(f4,axiom,(
% 1.81/0.61    ! [X0] : k2_subset_1(X0) = X0),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.81/0.61  fof(f75,plain,(
% 1.81/0.61    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f5])).
% 1.81/0.61  fof(f5,axiom,(
% 1.81/0.61    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.81/0.61  fof(f1154,plain,(
% 1.81/0.61    ~sP7(sK2)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1153,f68])).
% 1.81/0.61  fof(f1153,plain,(
% 1.81/0.61    ~sP7(sK2) | v2_struct_0(sK1)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1152,f71])).
% 1.81/0.61  fof(f1152,plain,(
% 1.81/0.61    ~sP7(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1148,f70])).
% 1.81/0.61  fof(f1148,plain,(
% 1.81/0.61    ~sP7(sK2) | ~v1_tdlat_3(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.81/0.61    inference(resolution,[],[f1104,f172])).
% 1.81/0.61  fof(f172,plain,(
% 1.81/0.61    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.61    inference(subsumption_resolution,[],[f104,f112])).
% 1.81/0.61  fof(f104,plain,(
% 1.81/0.61    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~v1_tdlat_3(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.61    inference(equality_resolution,[],[f83])).
% 1.81/0.61  fof(f83,plain,(
% 1.81/0.61    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_tdlat_3(X0) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f53])).
% 1.81/0.61  fof(f53,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_tdlat_3(X0)) & (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0))) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.81/0.61    inference(nnf_transformation,[],[f33])).
% 1.81/0.61  fof(f33,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.81/0.61    inference(flattening,[],[f32])).
% 1.81/0.61  fof(f32,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f17])).
% 1.81/0.61  fof(f17,axiom,(
% 1.81/0.61    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).
% 1.81/0.61  fof(f1104,plain,(
% 1.81/0.61    ~v2_tex_2(u1_struct_0(sK1),sK1) | ~sP7(sK2)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1095,f73])).
% 1.81/0.61  fof(f1095,plain,(
% 1.81/0.61    v2_tex_2(sK2,sK1) | ~v2_tex_2(u1_struct_0(sK1),sK1) | ~sP7(sK2)),
% 1.81/0.61    inference(superposition,[],[f445,f1013])).
% 1.81/0.61  fof(f1013,plain,(
% 1.81/0.61    ( ! [X8,X7] : (k3_xboole_0(X8,X7) = X7 | ~sP7(X7)) )),
% 1.81/0.61    inference(duplicate_literal_removal,[],[f1000])).
% 1.81/0.61  fof(f1000,plain,(
% 1.81/0.61    ( ! [X8,X7] : (~sP7(X7) | k3_xboole_0(X8,X7) = X7 | ~sP7(X7)) )),
% 1.81/0.61    inference(resolution,[],[f994,f130])).
% 1.81/0.61  fof(f130,plain,(
% 1.81/0.61    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~sP7(X2)) )),
% 1.81/0.61    inference(resolution,[],[f94,f119])).
% 1.81/0.61  fof(f119,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~sP7(X0)) )),
% 1.81/0.61    inference(resolution,[],[f96,f111])).
% 1.81/0.61  fof(f111,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP7(X1)) )),
% 1.81/0.61    inference(general_splitting,[],[f103,f110_D])).
% 1.81/0.61  fof(f103,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f45])).
% 1.81/0.61  fof(f45,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f10])).
% 1.81/0.61  fof(f10,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.81/0.61  fof(f96,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f66])).
% 1.81/0.61  fof(f66,plain,(
% 1.81/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f64,f65])).
% 1.81/0.61  fof(f65,plain,(
% 1.81/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f64,plain,(
% 1.81/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.81/0.61    inference(rectify,[],[f63])).
% 1.81/0.61  fof(f63,plain,(
% 1.81/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.81/0.61    inference(nnf_transformation,[],[f40])).
% 1.81/0.61  fof(f40,plain,(
% 1.81/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f1])).
% 1.81/0.61  fof(f1,axiom,(
% 1.81/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.81/0.61  fof(f94,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f62])).
% 1.81/0.61  fof(f62,plain,(
% 1.81/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.61    inference(flattening,[],[f61])).
% 1.81/0.61  fof(f61,plain,(
% 1.81/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.61    inference(nnf_transformation,[],[f2])).
% 1.81/0.61  fof(f2,axiom,(
% 1.81/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.81/0.61  fof(f994,plain,(
% 1.81/0.61    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(X4,X3),X3) | ~sP7(X3)) )),
% 1.81/0.61    inference(superposition,[],[f948,f228])).
% 1.81/0.61  fof(f228,plain,(
% 1.81/0.61    ( ! [X5] : (sK5(k1_zfmisc_1(X5)) = X5 | ~sP7(X5)) )),
% 1.81/0.61    inference(resolution,[],[f130,f114])).
% 1.81/0.61  fof(f114,plain,(
% 1.81/0.61    ( ! [X0] : (r1_tarski(sK5(k1_zfmisc_1(X0)),X0)) )),
% 1.81/0.61    inference(resolution,[],[f98,f91])).
% 1.81/0.61  fof(f91,plain,(
% 1.81/0.61    ( ! [X0] : (m1_subset_1(sK5(X0),X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f60])).
% 1.81/0.61  fof(f60,plain,(
% 1.81/0.61    ! [X0] : m1_subset_1(sK5(X0),X0)),
% 1.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f7,f59])).
% 1.81/0.61  fof(f59,plain,(
% 1.81/0.61    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK5(X0),X0))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f7,axiom,(
% 1.81/0.61    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.81/0.61  fof(f98,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f67])).
% 1.81/0.61  fof(f67,plain,(
% 1.81/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.81/0.61    inference(nnf_transformation,[],[f9])).
% 1.81/0.61  fof(f9,axiom,(
% 1.81/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.81/0.61  fof(f948,plain,(
% 1.81/0.61    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X2,sK5(k1_zfmisc_1(X3))),X3)) )),
% 1.81/0.61    inference(resolution,[],[f365,f112])).
% 1.81/0.61  fof(f365,plain,(
% 1.81/0.61    ( ! [X24,X23,X22] : (~m1_subset_1(X22,k1_zfmisc_1(sK5(k1_zfmisc_1(X23)))) | r1_tarski(k3_xboole_0(X24,X22),X23)) )),
% 1.81/0.61    inference(resolution,[],[f246,f137])).
% 1.81/0.61  fof(f137,plain,(
% 1.81/0.61    ( ! [X6,X7] : (~r1_tarski(X6,sK5(k1_zfmisc_1(X7))) | r1_tarski(X6,X7)) )),
% 1.81/0.61    inference(resolution,[],[f102,f114])).
% 1.81/0.61  fof(f102,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f44])).
% 1.81/0.61  fof(f44,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.81/0.61    inference(flattening,[],[f43])).
% 1.81/0.61  fof(f43,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.81/0.61    inference(ennf_transformation,[],[f3])).
% 1.81/0.61  fof(f3,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.81/0.61  fof(f246,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.81/0.61    inference(duplicate_literal_removal,[],[f245])).
% 1.81/0.61  fof(f245,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.81/0.61    inference(superposition,[],[f143,f101])).
% 1.81/0.61  fof(f101,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f42])).
% 1.81/0.61  fof(f42,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f8])).
% 1.81/0.61  fof(f8,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.81/0.61  fof(f143,plain,(
% 1.81/0.61    ( ! [X4,X5,X3] : (r1_tarski(k9_subset_1(X4,X5,X3),X4) | ~m1_subset_1(X3,k1_zfmisc_1(X4))) )),
% 1.81/0.61    inference(resolution,[],[f100,f98])).
% 1.81/0.61  fof(f100,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f41])).
% 1.81/0.61  fof(f41,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f6])).
% 1.81/0.61  fof(f6,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.81/0.61  fof(f445,plain,(
% 1.81/0.61    v2_tex_2(k3_xboole_0(u1_struct_0(sK1),sK2),sK1) | ~v2_tex_2(u1_struct_0(sK1),sK1)),
% 1.81/0.61    inference(resolution,[],[f357,f112])).
% 1.81/0.61  fof(f357,plain,(
% 1.81/0.61    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK1))) | v2_tex_2(k3_xboole_0(X16,sK2),sK1) | ~v2_tex_2(X16,sK1)) )),
% 1.81/0.61    inference(subsumption_resolution,[],[f349,f71])).
% 1.81/0.61  fof(f349,plain,(
% 1.81/0.61    ( ! [X16] : (~v2_tex_2(X16,sK1) | v2_tex_2(k3_xboole_0(X16,sK2),sK1) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) )),
% 1.81/0.61    inference(resolution,[],[f222,f72])).
% 1.81/0.61  fof(f222,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_tex_2(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.81/0.61    inference(duplicate_literal_removal,[],[f221])).
% 1.81/0.61  fof(f221,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (v2_tex_2(k3_xboole_0(X1,X2),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.81/0.61    inference(superposition,[],[f78,f101])).
% 1.81/0.61  fof(f78,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f30])).
% 1.81/0.61  fof(f30,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.81/0.61    inference(flattening,[],[f29])).
% 1.81/0.61  fof(f29,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.81/0.61    inference(ennf_transformation,[],[f18])).
% 1.81/0.61  fof(f18,axiom,(
% 1.81/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 1.81/0.61  % SZS output end Proof for theBenchmark
% 1.81/0.61  % (21204)------------------------------
% 1.81/0.61  % (21204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (21204)Termination reason: Refutation
% 1.81/0.61  
% 1.81/0.61  % (21204)Memory used [KB]: 2302
% 1.81/0.61  % (21204)Time elapsed: 0.173 s
% 1.81/0.61  % (21204)------------------------------
% 1.81/0.61  % (21204)------------------------------
% 1.81/0.61  % (21169)Success in time 0.243 s
%------------------------------------------------------------------------------
