%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 880 expanded)
%              Number of leaves         :   22 ( 267 expanded)
%              Depth                    :   20
%              Number of atoms          :  447 (3983 expanded)
%              Number of equality atoms :   36 ( 645 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f221,f242,f250,f262,f281,f286,f318,f323,f328])).

fof(f328,plain,
    ( ~ spl2_14
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl2_14
    | ~ spl2_17
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(global_subsumption,[],[f269,f324,f261])).

fof(f261,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK0)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl2_19
  <=> v1_tops_2(u1_pre_topc(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f324,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl2_14
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(subsumption_resolution,[],[f319,f308])).

fof(f308,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | ~ spl2_14
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f294,f96])).

fof(f96,plain,(
    u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f95,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ v1_tdlat_3(sK1)
    & v1_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f39,f38])).

% (578)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f38,plain,
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

fof(f39,plain,
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

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v1_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v1_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v1_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v1_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).

fof(f95,plain,
    ( u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f50])).

fof(f50,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(f294,plain,
    ( u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK0))
    | ~ spl2_14
    | ~ spl2_21 ),
    inference(superposition,[],[f99,f289])).

fof(f289,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_14
    | ~ spl2_21 ),
    inference(subsumption_resolution,[],[f288,f285])).

fof(f285,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl2_21
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f288,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl2_14 ),
    inference(resolution,[],[f220,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f220,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl2_14
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f99,plain,(
    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f98,f51])).

fof(f51,plain,(
    ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,
    ( u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1))
    | v1_tdlat_3(sK1) ),
    inference(resolution,[],[f57,f48])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f319,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl2_17 ),
    inference(resolution,[],[f246,f71])).

fof(f246,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl2_17
  <=> r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f269,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f254,f47])).

fof(f254,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f230,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(f230,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f225,f47])).

fof(f225,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f191,f139])).

fof(f139,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK1,X1)
      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f82,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

fof(f82,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(resolution,[],[f53,f48])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f191,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f190,f48])).

fof(f190,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f184,f47])).

fof(f184,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f117,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f117,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f116,f49])).

fof(f49,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f116,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f115,f48])).

fof(f115,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f77,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f52,f48])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f323,plain,(
    ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f321,f167])).

fof(f167,plain,(
    m1_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f108,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f104,f48])).

fof(f104,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f65,f49])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f108,plain,(
    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f107,f47])).

fof(f107,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f58,f76])).

fof(f76,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f52,f47])).

fof(f321,plain,
    ( ~ m1_pre_topc(sK0,sK1)
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f320,f48])).

fof(f320,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ spl2_18 ),
    inference(resolution,[],[f257,f151])).

fof(f151,plain,(
    v1_tops_2(u1_pre_topc(sK1),sK1) ),
    inference(subsumption_resolution,[],[f150,f48])).

fof(f150,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f140,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f140,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f82,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(u1_pre_topc(sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl2_18
  <=> ! [X0] :
        ( ~ v1_tops_2(u1_pre_topc(sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f318,plain,(
    ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f316,f191])).

fof(f316,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f315,f47])).

fof(f315,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl2_15 ),
    inference(resolution,[],[f237,f137])).

fof(f137,plain,(
    v1_tops_2(u1_pre_topc(sK0),sK0) ),
    inference(subsumption_resolution,[],[f136,f47])).

fof(f136,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f126,f73])).

fof(f126,plain,
    ( ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0))
    | v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f81,f63])).

fof(f81,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f53,f47])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl2_15
  <=> ! [X0] :
        ( ~ v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f286,plain,
    ( spl2_13
    | spl2_21 ),
    inference(avatar_split_clause,[],[f227,f283,f215])).

fof(f215,plain,
    ( spl2_13
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f227,plain,(
    ! [X0] :
      ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_pre_topc(sK0,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f191,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f281,plain,(
    ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f279,f76])).

fof(f279,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f278,f47])).

fof(f278,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f273,f79])).

fof(f79,plain,(
    v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f78,f47])).

fof(f78,plain,
    ( v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f50])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f273,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl2_13 ),
    inference(resolution,[],[f216,f191])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f215])).

fof(f262,plain,
    ( spl2_18
    | spl2_19 ),
    inference(avatar_split_clause,[],[f251,f259,f256])).

fof(f251,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(sK1),sK0)
      | ~ v1_tops_2(u1_pre_topc(sK1),X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f230,f75])).

fof(f75,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v1_tops_2(X3,X2)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f72,f61])).

% (574)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f72,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f250,plain,
    ( spl2_17
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f249,f239,f245])).

fof(f239,plain,
    ( spl2_16
  <=> v1_tops_2(u1_pre_topc(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f249,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK1)
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f234,f48])).

fof(f234,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK1)
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f213,f62])).

fof(f213,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f208,f48])).

fof(f208,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f167,f125])).

fof(f125,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK0,X1)
      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f81,f61])).

fof(f242,plain,
    ( spl2_15
    | spl2_16 ),
    inference(avatar_split_clause,[],[f231,f239,f236])).

fof(f231,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(sK0),sK1)
      | ~ v1_tops_2(u1_pre_topc(sK0),X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f213,f75])).

fof(f221,plain,
    ( spl2_13
    | spl2_14 ),
    inference(avatar_split_clause,[],[f210,f218,f215])).

fof(f210,plain,(
    ! [X0] :
      ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f167,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:11:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (575)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.49  % (554)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (556)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (577)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (555)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (565)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (563)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (552)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (563)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f221,f242,f250,f262,f281,f286,f318,f323,f328])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    ~spl2_14 | ~spl2_17 | ~spl2_19 | ~spl2_21),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f327])).
% 0.21/0.52  fof(f327,plain,(
% 0.21/0.52    $false | (~spl2_14 | ~spl2_17 | ~spl2_19 | ~spl2_21)),
% 0.21/0.52    inference(global_subsumption,[],[f269,f324,f261])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    v1_tops_2(u1_pre_topc(sK1),sK0) | ~spl2_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f259])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    spl2_19 <=> v1_tops_2(u1_pre_topc(sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.52  fof(f324,plain,(
% 0.21/0.52    ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | (~spl2_14 | ~spl2_17 | ~spl2_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f319,f308])).
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    u1_pre_topc(sK0) != u1_pre_topc(sK1) | (~spl2_14 | ~spl2_21)),
% 0.21/0.52    inference(forward_demodulation,[],[f294,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f95,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    (~v1_tdlat_3(sK1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f39,f38])).
% 0.21/0.52  % (578)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) => (~v1_tdlat_3(sK1) & v1_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~v1_tdlat_3(X1) & v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v1_tdlat_3(X1) & (v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v1_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tdlat_3(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f56,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    v1_tdlat_3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_tdlat_3(X0) | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0] : (((v1_tdlat_3(X0) | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))) & (u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : ((v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).
% 0.21/0.52  fof(f294,plain,(
% 0.21/0.52    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK0)) | (~spl2_14 | ~spl2_21)),
% 0.21/0.52    inference(superposition,[],[f99,f289])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(sK1) | (~spl2_14 | ~spl2_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f288,f285])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl2_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f283])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    spl2_21 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.52  fof(f288,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(sK1) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl2_14),
% 0.21/0.52    inference(resolution,[],[f220,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl2_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f218])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    spl2_14 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f98,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ~v1_tdlat_3(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1)) | v1_tdlat_3(sK1)),
% 0.21/0.52    inference(resolution,[],[f57,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) | v1_tdlat_3(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~spl2_17),
% 0.21/0.52    inference(resolution,[],[f246,f71])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~spl2_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f245])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    spl2_17 <=> r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    ~v1_tops_2(u1_pre_topc(sK1),sK0) | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f254,f47])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    ~v1_tops_2(u1_pre_topc(sK1),sK0) | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f230,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0) | r1_tarski(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f225,f47])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f191,f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_pre_topc(sK1,X1) | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~l1_pre_topc(X1)) )),
% 0.21/0.52    inference(resolution,[],[f82,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.52    inference(resolution,[],[f53,f48])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f190,f48])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f184,f47])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f117,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    inference(forward_demodulation,[],[f116,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f115,f48])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f77,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK1)),
% 0.21/0.52    inference(resolution,[],[f52,f48])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.52  fof(f323,plain,(
% 0.21/0.52    ~spl2_18),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f322])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    $false | ~spl2_18),
% 0.21/0.52    inference(subsumption_resolution,[],[f321,f167])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    m1_pre_topc(sK0,sK1)),
% 0.21/0.52    inference(resolution,[],[f108,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f104,f48])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f65,f49])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f47])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f58,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    m1_pre_topc(sK0,sK0)),
% 0.21/0.52    inference(resolution,[],[f52,f47])).
% 0.21/0.52  fof(f321,plain,(
% 0.21/0.52    ~m1_pre_topc(sK0,sK1) | ~spl2_18),
% 0.21/0.52    inference(subsumption_resolution,[],[f320,f48])).
% 0.21/0.52  fof(f320,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,sK1) | ~spl2_18),
% 0.21/0.52    inference(resolution,[],[f257,f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    v1_tops_2(u1_pre_topc(sK1),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f150,f48])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    v1_tops_2(u1_pre_topc(sK1),sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f140,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) | v1_tops_2(u1_pre_topc(sK1),sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f82,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_tops_2(u1_pre_topc(sK1),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0)) ) | ~spl2_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f256])).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    spl2_18 <=> ! [X0] : (~v1_tops_2(u1_pre_topc(sK1),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.52  fof(f318,plain,(
% 0.21/0.52    ~spl2_15),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f317])).
% 0.21/0.52  fof(f317,plain,(
% 0.21/0.52    $false | ~spl2_15),
% 0.21/0.52    inference(subsumption_resolution,[],[f316,f191])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    ~m1_pre_topc(sK1,sK0) | ~spl2_15),
% 0.21/0.52    inference(subsumption_resolution,[],[f315,f47])).
% 0.21/0.52  fof(f315,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~spl2_15),
% 0.21/0.52    inference(resolution,[],[f237,f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    v1_tops_2(u1_pre_topc(sK0),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f136,f47])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    v1_tops_2(u1_pre_topc(sK0),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f126,f73])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ~r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) | v1_tops_2(u1_pre_topc(sK0),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f81,f63])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    inference(resolution,[],[f53,f47])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_tops_2(u1_pre_topc(sK0),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0)) ) | ~spl2_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f236])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    spl2_15 <=> ! [X0] : (~v1_tops_2(u1_pre_topc(sK0),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    spl2_13 | spl2_21),
% 0.21/0.52    inference(avatar_split_clause,[],[f227,f283,f215])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    spl2_13 <=> ! [X0] : (~m1_pre_topc(sK1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(resolution,[],[f191,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    ~spl2_13),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f280])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    $false | ~spl2_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f279,f76])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    ~m1_pre_topc(sK0,sK0) | ~spl2_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f278,f47])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK0,sK0) | ~spl2_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f273,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f47])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    v2_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f54,f50])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK0,sK0) | ~spl2_13),
% 0.21/0.52    inference(resolution,[],[f216,f191])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0)) ) | ~spl2_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f215])).
% 0.21/0.52  fof(f262,plain,(
% 0.21/0.52    spl2_18 | spl2_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f251,f259,f256])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    ( ! [X0] : (v1_tops_2(u1_pre_topc(sK1),sK0) | ~v1_tops_2(u1_pre_topc(sK1),X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(resolution,[],[f230,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | v1_tops_2(X3,X2) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f72,f61])).
% 0.21/0.52  % (574)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    spl2_17 | ~spl2_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f249,f239,f245])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    spl2_16 <=> v1_tops_2(u1_pre_topc(sK0),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    ~v1_tops_2(u1_pre_topc(sK0),sK1) | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f234,f48])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    ~v1_tops_2(u1_pre_topc(sK0),sK1) | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f213,f62])).
% 0.21/0.52  fof(f213,plain,(
% 0.21/0.52    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f208,f48])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f167,f125])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_pre_topc(sK0,X1) | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~l1_pre_topc(X1)) )),
% 0.21/0.52    inference(resolution,[],[f81,f61])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    spl2_15 | spl2_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f231,f239,f236])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ( ! [X0] : (v1_tops_2(u1_pre_topc(sK0),sK1) | ~v1_tops_2(u1_pre_topc(sK0),X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(resolution,[],[f213,f75])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    spl2_13 | spl2_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f210,f218,f215])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(resolution,[],[f167,f68])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (563)------------------------------
% 0.21/0.52  % (563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (563)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (563)Memory used [KB]: 10746
% 0.21/0.52  % (563)Time elapsed: 0.110 s
% 0.21/0.52  % (563)------------------------------
% 0.21/0.52  % (563)------------------------------
% 0.21/0.52  % (551)Success in time 0.161 s
%------------------------------------------------------------------------------
