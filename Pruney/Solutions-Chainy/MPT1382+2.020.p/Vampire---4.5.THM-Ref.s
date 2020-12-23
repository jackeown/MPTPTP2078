%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 513 expanded)
%              Number of leaves         :   10 (  93 expanded)
%              Depth                    :   21
%              Number of atoms          :  314 (3819 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f329,f345,f357])).

fof(f357,plain,(
    ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f355,f249])).

fof(f249,plain,(
    ~ sP5(sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f243,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f39,f40_D])).

fof(f40,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f40_D])).

fof(f40_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f243,plain,(
    r2_hidden(sK1,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f240,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | r2_hidden(X0,sK3(sK0,X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f120,f24])).

fof(f24,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_tarski(X3,X2)
                            & v3_pre_topc(X3,X0)
                            & m1_connsp_2(X3,X0,X1) ) )
                    & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f120,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | r2_hidden(X0,sK3(sK0,X0,sK2))
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f118,f25])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

% (21197)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
fof(f118,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | r2_hidden(X0,sK3(sK0,X0,sK2))
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2)) ) ),
    inference(resolution,[],[f32,f20])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X1,sK3(X0,X1,X2))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(f240,plain,(
    r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f239,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f239,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f235,f21])).

fof(f21,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f235,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(sK2,sK0,X3)
      | r2_hidden(X3,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f234,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f234,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X3,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X3) ) ),
    inference(subsumption_resolution,[],[f233,f25])).

fof(f233,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X3,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X3) ) ),
    inference(subsumption_resolution,[],[f228,f24])).

fof(f228,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X3,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X3) ) ),
    inference(resolution,[],[f27,f20])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f355,plain,
    ( sP5(sK3(sK0,sK1,sK2))
    | ~ spl6_17 ),
    inference(resolution,[],[f328,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sP5(X0) ) ),
    inference(resolution,[],[f40,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f61,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f61,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f328,plain,
    ( v1_xboole_0(sK3(sK0,sK1,sK2))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl6_17
  <=> v1_xboole_0(sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f345,plain,(
    spl6_16 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl6_16 ),
    inference(subsumption_resolution,[],[f343,f324])).

fof(f324,plain,
    ( ~ m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl6_16
  <=> m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f343,plain,(
    m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1) ),
    inference(subsumption_resolution,[],[f342,f22])).

fof(f342,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1) ),
    inference(resolution,[],[f283,f243])).

fof(f283,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3(sK0,sK1,sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,X2) ) ),
    inference(subsumption_resolution,[],[f282,f245])).

fof(f245,plain,(
    v3_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f240,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | v3_pre_topc(sK3(sK0,X0,sK2),sK0) ) ),
    inference(subsumption_resolution,[],[f97,f24])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v3_pre_topc(sK3(sK0,X0,sK2),sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f95,f25])).

fof(f95,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v3_pre_topc(sK3(sK0,X0,sK2),sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2)) ) ),
    inference(resolution,[],[f30,f20])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f282,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK3(sK0,sK1,sK2),sK0)
      | ~ r2_hidden(X2,sK3(sK0,sK1,sK2))
      | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,X2) ) ),
    inference(subsumption_resolution,[],[f281,f23])).

fof(f281,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK3(sK0,sK1,sK2),sK0)
      | ~ r2_hidden(X2,sK3(sK0,sK1,sK2))
      | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,X2) ) ),
    inference(subsumption_resolution,[],[f280,f25])).

fof(f280,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK3(sK0,sK1,sK2),sK0)
      | ~ r2_hidden(X2,sK3(sK0,sK1,sK2))
      | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,X2) ) ),
    inference(subsumption_resolution,[],[f265,f24])).

fof(f265,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK3(sK0,sK1,sK2),sK0)
      | ~ r2_hidden(X2,sK3(sK0,sK1,sK2))
      | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,X2) ) ),
    inference(resolution,[],[f242,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f242,plain,(
    m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f240,f137])).

fof(f137,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_tops_1(sK0,sK2))
      | m1_subset_1(sK3(sK0,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f136,f24])).

fof(f136,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK0)
      | m1_subset_1(sK3(sK0,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,k1_tops_1(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f135,f25])).

fof(f135,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK3(sK0,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,k1_tops_1(sK0,sK2)) ) ),
    inference(resolution,[],[f29,f20])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f329,plain,
    ( ~ spl6_16
    | spl6_17 ),
    inference(avatar_split_clause,[],[f273,f326,f322])).

fof(f273,plain,
    ( v1_xboole_0(sK3(sK0,sK1,sK2))
    | ~ m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1) ),
    inference(subsumption_resolution,[],[f272,f244])).

fof(f244,plain,(
    r1_tarski(sK3(sK0,sK1,sK2),sK2) ),
    inference(resolution,[],[f240,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | r1_tarski(sK3(sK0,X0,sK2),sK2) ) ),
    inference(subsumption_resolution,[],[f116,f24])).

fof(f116,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | r1_tarski(sK3(sK0,X0,sK2),sK2)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f114,f25])).

fof(f114,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | r1_tarski(sK3(sK0,X0,sK2),sK2)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2)) ) ),
    inference(resolution,[],[f31,f20])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r1_tarski(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f272,plain,
    ( v1_xboole_0(sK3(sK0,sK1,sK2))
    | ~ m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1)
    | ~ r1_tarski(sK3(sK0,sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f262,f245])).

fof(f262,plain,
    ( v1_xboole_0(sK3(sK0,sK1,sK2))
    | ~ m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1)
    | ~ v3_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | ~ r1_tarski(sK3(sK0,sK1,sK2),sK2) ),
    inference(resolution,[],[f242,f19])).

fof(f19,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK2) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (21202)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.44  % (21189)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.45  % (21189)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f358,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f329,f345,f357])).
% 0.20/0.45  fof(f357,plain,(
% 0.20/0.45    ~spl6_17),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f356])).
% 0.20/0.45  fof(f356,plain,(
% 0.20/0.45    $false | ~spl6_17),
% 0.20/0.45    inference(subsumption_resolution,[],[f355,f249])).
% 0.20/0.45  fof(f249,plain,(
% 0.20/0.45    ~sP5(sK3(sK0,sK1,sK2))),
% 0.20/0.45    inference(resolution,[],[f243,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP5(X1)) )),
% 0.20/0.45    inference(general_splitting,[],[f39,f40_D])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP5(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f40_D])).
% 0.20/0.45  fof(f40_D,plain,(
% 0.20/0.45    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP5(X1)) )),
% 0.20/0.45    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.45  fof(f243,plain,(
% 0.20/0.45    r2_hidden(sK1,sK3(sK0,sK1,sK2))),
% 0.20/0.45    inference(resolution,[],[f240,f121])).
% 0.20/0.45  fof(f121,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | r2_hidden(X0,sK3(sK0,X0,sK2))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f120,f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    v2_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,negated_conjecture,(
% 0.20/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.45    inference(negated_conjecture,[],[f7])).
% 0.20/0.45  fof(f7,conjecture,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.20/0.45  fof(f120,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_pre_topc(sK0) | r2_hidden(X0,sK3(sK0,X0,sK2)) | ~r2_hidden(X0,k1_tops_1(sK0,sK2))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f118,f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  % (21197)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r2_hidden(X0,sK3(sK0,X0,sK2)) | ~r2_hidden(X0,k1_tops_1(sK0,sK2))) )),
% 0.20/0.45    inference(resolution,[],[f32,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X1,sK3(X0,X1,X2)) | ~r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).
% 0.20/0.45  fof(f240,plain,(
% 0.20/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.20/0.45    inference(subsumption_resolution,[],[f239,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f239,plain,(
% 0.20/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.45    inference(resolution,[],[f235,f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f235,plain,(
% 0.20/0.45    ( ! [X3] : (~m1_connsp_2(sK2,sK0,X3) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f234,f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f234,plain,(
% 0.20/0.45    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X3)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f233,f25])).
% 0.20/0.45  fof(f233,plain,(
% 0.20/0.45    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X3)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f228,f24])).
% 0.20/0.45  fof(f228,plain,(
% 0.20/0.45    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X3,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X3)) )),
% 0.20/0.45    inference(resolution,[],[f27,f20])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.20/0.45  fof(f355,plain,(
% 0.20/0.45    sP5(sK3(sK0,sK1,sK2)) | ~spl6_17),
% 0.20/0.45    inference(resolution,[],[f328,f68])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_xboole_0(X0) | sP5(X0)) )),
% 0.20/0.45    inference(resolution,[],[f40,f63])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(resolution,[],[f61,f37])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f60])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.20/0.45    inference(resolution,[],[f36,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f328,plain,(
% 0.20/0.45    v1_xboole_0(sK3(sK0,sK1,sK2)) | ~spl6_17),
% 0.20/0.45    inference(avatar_component_clause,[],[f326])).
% 0.20/0.45  fof(f326,plain,(
% 0.20/0.45    spl6_17 <=> v1_xboole_0(sK3(sK0,sK1,sK2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.45  fof(f345,plain,(
% 0.20/0.45    spl6_16),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f344])).
% 0.20/0.45  fof(f344,plain,(
% 0.20/0.45    $false | spl6_16),
% 0.20/0.45    inference(subsumption_resolution,[],[f343,f324])).
% 0.20/0.45  fof(f324,plain,(
% 0.20/0.45    ~m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1) | spl6_16),
% 0.20/0.45    inference(avatar_component_clause,[],[f322])).
% 0.20/0.45  fof(f322,plain,(
% 0.20/0.45    spl6_16 <=> m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.45  fof(f343,plain,(
% 0.20/0.45    m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f342,f22])).
% 0.20/0.45  fof(f342,plain,(
% 0.20/0.45    ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1)),
% 0.20/0.45    inference(resolution,[],[f283,f243])).
% 0.20/0.45  fof(f283,plain,(
% 0.20/0.45    ( ! [X2] : (~r2_hidden(X2,sK3(sK0,sK1,sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,X2)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f282,f245])).
% 0.20/0.45  fof(f245,plain,(
% 0.20/0.45    v3_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.20/0.45    inference(resolution,[],[f240,f98])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | v3_pre_topc(sK3(sK0,X0,sK2),sK0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f97,f24])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_pre_topc(sK0) | v3_pre_topc(sK3(sK0,X0,sK2),sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK2))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f95,f25])).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(sK3(sK0,X0,sK2),sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK2))) )),
% 0.20/0.45    inference(resolution,[],[f30,f20])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(sK3(X0,X1,X2),X0) | ~r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f282,plain,(
% 0.20/0.45    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~v3_pre_topc(sK3(sK0,sK1,sK2),sK0) | ~r2_hidden(X2,sK3(sK0,sK1,sK2)) | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,X2)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f281,f23])).
% 0.20/0.45  fof(f281,plain,(
% 0.20/0.45    ( ! [X2] : (v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v3_pre_topc(sK3(sK0,sK1,sK2),sK0) | ~r2_hidden(X2,sK3(sK0,sK1,sK2)) | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,X2)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f280,f25])).
% 0.20/0.45  fof(f280,plain,(
% 0.20/0.45    ( ! [X2] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v3_pre_topc(sK3(sK0,sK1,sK2),sK0) | ~r2_hidden(X2,sK3(sK0,sK1,sK2)) | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,X2)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f265,f24])).
% 0.20/0.45  fof(f265,plain,(
% 0.20/0.45    ( ! [X2] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v3_pre_topc(sK3(sK0,sK1,sK2),sK0) | ~r2_hidden(X2,sK3(sK0,sK1,sK2)) | m1_connsp_2(sK3(sK0,sK1,sK2),sK0,X2)) )),
% 0.20/0.45    inference(resolution,[],[f242,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.20/0.45  fof(f242,plain,(
% 0.20/0.45    m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(resolution,[],[f240,f137])).
% 0.20/0.45  fof(f137,plain,(
% 0.20/0.45    ( ! [X2] : (~r2_hidden(X2,k1_tops_1(sK0,sK2)) | m1_subset_1(sK3(sK0,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f136,f24])).
% 0.20/0.45  fof(f136,plain,(
% 0.20/0.45    ( ! [X2] : (~v2_pre_topc(sK0) | m1_subset_1(sK3(sK0,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,k1_tops_1(sK0,sK2))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f135,f25])).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    ( ! [X2] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK3(sK0,X2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,k1_tops_1(sK0,sK2))) )),
% 0.20/0.45    inference(resolution,[],[f29,f20])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f329,plain,(
% 0.20/0.45    ~spl6_16 | spl6_17),
% 0.20/0.45    inference(avatar_split_clause,[],[f273,f326,f322])).
% 0.20/0.45  fof(f273,plain,(
% 0.20/0.45    v1_xboole_0(sK3(sK0,sK1,sK2)) | ~m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f272,f244])).
% 0.20/0.45  fof(f244,plain,(
% 0.20/0.45    r1_tarski(sK3(sK0,sK1,sK2),sK2)),
% 0.20/0.45    inference(resolution,[],[f240,f117])).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | r1_tarski(sK3(sK0,X0,sK2),sK2)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f116,f24])).
% 0.20/0.45  fof(f116,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_pre_topc(sK0) | r1_tarski(sK3(sK0,X0,sK2),sK2) | ~r2_hidden(X0,k1_tops_1(sK0,sK2))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f114,f25])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK3(sK0,X0,sK2),sK2) | ~r2_hidden(X0,k1_tops_1(sK0,sK2))) )),
% 0.20/0.45    inference(resolution,[],[f31,f20])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r1_tarski(sK3(X0,X1,X2),X2) | ~r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f272,plain,(
% 0.20/0.45    v1_xboole_0(sK3(sK0,sK1,sK2)) | ~m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1) | ~r1_tarski(sK3(sK0,sK1,sK2),sK2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f262,f245])).
% 0.20/0.45  fof(f262,plain,(
% 0.20/0.45    v1_xboole_0(sK3(sK0,sK1,sK2)) | ~m1_connsp_2(sK3(sK0,sK1,sK2),sK0,sK1) | ~v3_pre_topc(sK3(sK0,sK1,sK2),sK0) | ~r1_tarski(sK3(sK0,sK1,sK2),sK2)),
% 0.20/0.45    inference(resolution,[],[f242,f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3) | ~m1_connsp_2(X3,sK0,sK1) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (21189)------------------------------
% 0.20/0.45  % (21189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (21189)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (21189)Memory used [KB]: 5500
% 0.20/0.45  % (21189)Time elapsed: 0.045 s
% 0.20/0.45  % (21189)------------------------------
% 0.20/0.45  % (21189)------------------------------
% 0.20/0.46  % (21182)Success in time 0.097 s
%------------------------------------------------------------------------------
