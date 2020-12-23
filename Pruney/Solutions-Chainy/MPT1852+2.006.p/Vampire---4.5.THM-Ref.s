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
% DateTime   : Thu Dec  3 13:20:41 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 439 expanded)
%              Number of leaves         :   16 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          :  417 (1589 expanded)
%              Number of equality atoms :   18 ( 203 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (11036)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (11044)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f100,f165,f176,f212])).

fof(f212,plain,
    ( ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f210,f30])).

fof(f30,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).

fof(f210,plain,
    ( ~ v3_tdlat_3(sK0)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f209,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f209,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f208,f195])).

fof(f195,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f194,f31])).

fof(f31,plain,(
    ~ v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f194,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | v3_tdlat_3(sK1)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f189,f28])).

fof(f28,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f189,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | v3_tdlat_3(sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f37,f160])).

fof(f160,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl3_3
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(f208,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f204,f112])).

fof(f112,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f111,f31])).

fof(f111,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tdlat_3(sK1)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f107,f28])).

fof(f107,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | v3_tdlat_3(sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f36,f86])).

fof(f86,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_1
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f204,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f35,f177])).

fof(f177,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f110,f160])).

fof(f110,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f109,f31])).

fof(f109,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | v3_tdlat_3(sK1)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f106,f28])).

fof(f106,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v3_tdlat_3(sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f38,f86])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f176,plain,
    ( ~ spl3_1
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl3_1
    | spl3_4 ),
    inference(subsumption_resolution,[],[f174,f164])).

fof(f164,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl3_4
  <=> r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f174,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f173,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f173,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f171,f113])).

fof(f113,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f108,f28])).

fof(f108,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f34,f86])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f171,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X2,u1_pre_topc(sK1))
        | r1_tarski(X2,u1_pre_topc(sK0)) )
    | ~ spl3_1 ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_pre_topc(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(X2,u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f167,f121])).

fof(f121,plain,(
    ! [X1] :
      ( ~ v1_tops_2(X1,sK0)
      | r1_tarski(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f45,f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f167,plain,
    ( ! [X1] :
        ( v1_tops_2(X1,sK0)
        | ~ r1_tarski(X1,u1_pre_topc(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f143,f56])).

fof(f56,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f33,f32])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f143,plain,
    ( ! [X2,X1] :
        ( ~ m1_pre_topc(X2,sK0)
        | v1_tops_2(X1,X2)
        | ~ r1_tarski(X1,u1_pre_topc(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f139,f92])).

fof(f92,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK1)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f76,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK1) ) ),
    inference(forward_demodulation,[],[f66,f29])).

fof(f29,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(X0,sK1) ) ),
    inference(resolution,[],[f47,f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f76,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f73,f58])).

fof(f58,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | l1_pre_topc(X1) ) ),
    inference(resolution,[],[f41,f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f73,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f40,f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v1_tops_2(X1,X0)
        | ~ r1_tarski(X1,u1_pre_topc(sK1)) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f138,f129])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f127,f86])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    inference(resolution,[],[f43,f28])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v1_tops_2(X1,X0)
        | ~ r1_tarski(X1,u1_pre_topc(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f136,f119])).

fof(f119,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,sK1)
        | ~ r1_tarski(X0,u1_pre_topc(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f117,f86])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | ~ r1_tarski(X0,u1_pre_topc(sK1))
      | v1_tops_2(X0,sK1) ) ),
    inference(resolution,[],[f44,f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X1,sK1)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0) ) ),
    inference(resolution,[],[f54,f28])).

fof(f54,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v1_tops_2(X3,X2) ) ),
    inference(subsumption_resolution,[],[f51,f43])).

fof(f51,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v1_tops_2(X3,X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | X1 != X3
      | v1_tops_2(X3,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

% (11040)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

fof(f165,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f156,f84,f162,f158])).

fof(f156,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f155,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f155,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f154,f32])).

fof(f154,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f152,f52])).

fof(f152,plain,
    ( ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0))
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f150,f34])).

fof(f150,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X2,u1_pre_topc(sK0))
        | r1_tarski(X2,u1_pre_topc(sK1)) )
    | ~ spl3_1 ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X2,u1_pre_topc(sK0))
        | r1_tarski(X2,u1_pre_topc(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f147,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(X0,sK1)
        | r1_tarski(X0,u1_pre_topc(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f120,f86])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | r1_tarski(X0,u1_pre_topc(sK1))
      | ~ v1_tops_2(X0,sK1) ) ),
    inference(resolution,[],[f45,f28])).

fof(f147,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,u1_pre_topc(sK0)) )
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f145,f86])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | v1_tops_2(X0,sK1)
      | ~ r1_tarski(X0,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f141,f79])).

fof(f79,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f33,f28])).

fof(f78,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | m1_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f75,f67])).

fof(f67,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f47,f32])).

fof(f75,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(forward_demodulation,[],[f74,f29])).

fof(f74,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f72,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f41,f28])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(resolution,[],[f40,f28])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(sK0)) ) ),
    inference(subsumption_resolution,[],[f140,f128])).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f43,f32])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f137,f118])).

fof(f118,plain,(
    ! [X1] :
      ( v1_tops_2(X1,sK0)
      | ~ r1_tarski(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f44,f32])).

fof(f137,plain,(
    ! [X2,X3] :
      ( ~ v1_tops_2(X3,sK0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v1_tops_2(X3,X2) ) ),
    inference(resolution,[],[f54,f32])).

fof(f100,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f98,f90])).

fof(f90,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_2
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f98,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f95,f56])).

fof(f95,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f92,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f42,f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f91,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f82,f88,f84])).

fof(f82,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(resolution,[],[f80,f50])).

fof(f80,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f79,f63])).

fof(f63,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f42,f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:10:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (11058)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (11039)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (11048)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (11055)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (11035)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (11041)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (11039)Refutation not found, incomplete strategy% (11039)------------------------------
% 0.22/0.52  % (11039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11039)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (11039)Memory used [KB]: 10618
% 0.22/0.52  % (11039)Time elapsed: 0.088 s
% 0.22/0.52  % (11039)------------------------------
% 0.22/0.52  % (11039)------------------------------
% 0.22/0.52  % (11049)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.17/0.52  % (11033)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.17/0.52  % (11057)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.17/0.52  % (11053)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.17/0.52  % (11055)Refutation found. Thanks to Tanya!
% 1.17/0.52  % SZS status Theorem for theBenchmark
% 1.17/0.52  % SZS output start Proof for theBenchmark
% 1.17/0.52  % (11036)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.17/0.52  % (11044)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.17/0.52  fof(f213,plain,(
% 1.17/0.52    $false),
% 1.17/0.52    inference(avatar_sat_refutation,[],[f91,f100,f165,f176,f212])).
% 1.17/0.52  fof(f212,plain,(
% 1.17/0.52    ~spl3_1 | ~spl3_3),
% 1.17/0.52    inference(avatar_contradiction_clause,[],[f211])).
% 1.17/0.52  fof(f211,plain,(
% 1.17/0.52    $false | (~spl3_1 | ~spl3_3)),
% 1.17/0.52    inference(subsumption_resolution,[],[f210,f30])).
% 1.17/0.52  fof(f30,plain,(
% 1.17/0.52    v3_tdlat_3(sK0)),
% 1.17/0.52    inference(cnf_transformation,[],[f15])).
% 1.17/0.52  fof(f15,plain,(
% 1.17/0.52    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.17/0.52    inference(flattening,[],[f14])).
% 1.17/0.52  fof(f14,plain,(
% 1.17/0.52    ? [X0] : (? [X1] : ((~v3_tdlat_3(X1) & (v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f13])).
% 1.17/0.52  fof(f13,negated_conjecture,(
% 1.17/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 1.17/0.52    inference(negated_conjecture,[],[f12])).
% 1.17/0.52  fof(f12,conjecture,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).
% 1.17/0.52  fof(f210,plain,(
% 1.17/0.52    ~v3_tdlat_3(sK0) | (~spl3_1 | ~spl3_3)),
% 1.17/0.52    inference(subsumption_resolution,[],[f209,f32])).
% 1.17/0.52  fof(f32,plain,(
% 1.17/0.52    l1_pre_topc(sK0)),
% 1.17/0.52    inference(cnf_transformation,[],[f15])).
% 1.17/0.52  fof(f209,plain,(
% 1.17/0.52    ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | (~spl3_1 | ~spl3_3)),
% 1.17/0.52    inference(subsumption_resolution,[],[f208,f195])).
% 1.17/0.52  fof(f195,plain,(
% 1.17/0.52    r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~spl3_3),
% 1.17/0.52    inference(subsumption_resolution,[],[f194,f31])).
% 1.17/0.52  fof(f31,plain,(
% 1.17/0.52    ~v3_tdlat_3(sK1)),
% 1.17/0.52    inference(cnf_transformation,[],[f15])).
% 1.17/0.52  fof(f194,plain,(
% 1.17/0.52    r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | v3_tdlat_3(sK1) | ~spl3_3),
% 1.17/0.52    inference(subsumption_resolution,[],[f189,f28])).
% 1.17/0.52  fof(f28,plain,(
% 1.17/0.52    l1_pre_topc(sK1)),
% 1.17/0.52    inference(cnf_transformation,[],[f15])).
% 1.17/0.52  fof(f189,plain,(
% 1.17/0.52    r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK1) | v3_tdlat_3(sK1) | ~spl3_3),
% 1.17/0.52    inference(superposition,[],[f37,f160])).
% 1.17/0.52  fof(f160,plain,(
% 1.17/0.52    u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~spl3_3),
% 1.17/0.52    inference(avatar_component_clause,[],[f158])).
% 1.17/0.52  fof(f158,plain,(
% 1.17/0.52    spl3_3 <=> u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.17/0.52  fof(f37,plain,(
% 1.17/0.52    ( ! [X0] : (r2_hidden(sK2(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | v3_tdlat_3(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f19])).
% 1.17/0.52  fof(f19,plain,(
% 1.17/0.52    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(flattening,[],[f18])).
% 1.17/0.52  fof(f18,plain,(
% 1.17/0.52    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f11])).
% 1.17/0.52  fof(f11,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))))))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).
% 1.17/0.52  fof(f208,plain,(
% 1.17/0.52    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | (~spl3_1 | ~spl3_3)),
% 1.17/0.52    inference(subsumption_resolution,[],[f204,f112])).
% 1.17/0.52  fof(f112,plain,(
% 1.17/0.52    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_1),
% 1.17/0.52    inference(subsumption_resolution,[],[f111,f31])).
% 1.17/0.52  fof(f111,plain,(
% 1.17/0.52    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tdlat_3(sK1) | ~spl3_1),
% 1.17/0.52    inference(subsumption_resolution,[],[f107,f28])).
% 1.17/0.52  fof(f107,plain,(
% 1.17/0.52    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK1) | v3_tdlat_3(sK1) | ~spl3_1),
% 1.17/0.52    inference(superposition,[],[f36,f86])).
% 1.17/0.52  fof(f86,plain,(
% 1.17/0.52    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl3_1),
% 1.17/0.52    inference(avatar_component_clause,[],[f84])).
% 1.17/0.52  fof(f84,plain,(
% 1.17/0.52    spl3_1 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.17/0.52  fof(f36,plain,(
% 1.17/0.52    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_tdlat_3(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f19])).
% 1.17/0.52  fof(f204,plain,(
% 1.17/0.52    ~m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | (~spl3_1 | ~spl3_3)),
% 1.17/0.52    inference(resolution,[],[f35,f177])).
% 1.17/0.52  fof(f177,plain,(
% 1.17/0.52    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | (~spl3_1 | ~spl3_3)),
% 1.17/0.52    inference(backward_demodulation,[],[f110,f160])).
% 1.17/0.52  fof(f110,plain,(
% 1.17/0.52    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | ~spl3_1),
% 1.17/0.52    inference(subsumption_resolution,[],[f109,f31])).
% 1.17/0.52  fof(f109,plain,(
% 1.17/0.52    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | v3_tdlat_3(sK1) | ~spl3_1),
% 1.17/0.52    inference(subsumption_resolution,[],[f106,f28])).
% 1.17/0.52  fof(f106,plain,(
% 1.17/0.52    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | v3_tdlat_3(sK1) | ~spl3_1),
% 1.17/0.52    inference(superposition,[],[f38,f86])).
% 1.17/0.52  fof(f38,plain,(
% 1.17/0.52    ( ! [X0] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | v3_tdlat_3(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f19])).
% 1.17/0.52  fof(f35,plain,(
% 1.17/0.52    ( ! [X0,X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f19])).
% 1.17/0.52  fof(f176,plain,(
% 1.17/0.52    ~spl3_1 | spl3_4),
% 1.17/0.52    inference(avatar_contradiction_clause,[],[f175])).
% 1.17/0.52  fof(f175,plain,(
% 1.17/0.52    $false | (~spl3_1 | spl3_4)),
% 1.17/0.52    inference(subsumption_resolution,[],[f174,f164])).
% 1.17/0.52  fof(f164,plain,(
% 1.17/0.52    ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | spl3_4),
% 1.17/0.52    inference(avatar_component_clause,[],[f162])).
% 1.17/0.52  fof(f162,plain,(
% 1.17/0.52    spl3_4 <=> r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.17/0.52  fof(f174,plain,(
% 1.17/0.52    r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~spl3_1),
% 1.17/0.52    inference(subsumption_resolution,[],[f173,f52])).
% 1.17/0.52  fof(f52,plain,(
% 1.17/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.17/0.52    inference(equality_resolution,[],[f49])).
% 1.17/0.52  fof(f49,plain,(
% 1.17/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.17/0.52    inference(cnf_transformation,[],[f1])).
% 1.17/0.52  fof(f1,axiom,(
% 1.17/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.17/0.52  fof(f173,plain,(
% 1.17/0.52    ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~spl3_1),
% 1.17/0.52    inference(resolution,[],[f171,f113])).
% 1.17/0.52  fof(f113,plain,(
% 1.17/0.52    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_1),
% 1.17/0.52    inference(subsumption_resolution,[],[f108,f28])).
% 1.17/0.52  fof(f108,plain,(
% 1.17/0.52    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK1) | ~spl3_1),
% 1.17/0.52    inference(superposition,[],[f34,f86])).
% 1.17/0.52  fof(f34,plain,(
% 1.17/0.52    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f17])).
% 1.17/0.52  fof(f17,plain,(
% 1.17/0.52    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f3])).
% 1.17/0.52  fof(f3,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.17/0.52  fof(f171,plain,(
% 1.17/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X2,u1_pre_topc(sK1)) | r1_tarski(X2,u1_pre_topc(sK0))) ) | ~spl3_1),
% 1.17/0.52    inference(duplicate_literal_removal,[],[f170])).
% 1.17/0.52  fof(f170,plain,(
% 1.17/0.52    ( ! [X2] : (~r1_tarski(X2,u1_pre_topc(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(X2,u1_pre_topc(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_1),
% 1.17/0.52    inference(resolution,[],[f167,f121])).
% 1.17/0.52  fof(f121,plain,(
% 1.17/0.52    ( ! [X1] : (~v1_tops_2(X1,sK0) | r1_tarski(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.17/0.52    inference(resolution,[],[f45,f32])).
% 1.17/0.52  fof(f45,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f24])).
% 1.17/0.52  fof(f24,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f8])).
% 1.17/0.52  fof(f8,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 1.17/0.52  fof(f167,plain,(
% 1.17/0.52    ( ! [X1] : (v1_tops_2(X1,sK0) | ~r1_tarski(X1,u1_pre_topc(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_1),
% 1.17/0.52    inference(resolution,[],[f143,f56])).
% 1.17/0.52  fof(f56,plain,(
% 1.17/0.52    m1_pre_topc(sK0,sK0)),
% 1.17/0.52    inference(resolution,[],[f33,f32])).
% 1.17/0.52  fof(f33,plain,(
% 1.17/0.52    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f16])).
% 1.17/0.52  fof(f16,plain,(
% 1.17/0.52    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f9])).
% 1.17/0.52  fof(f9,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.17/0.52  fof(f143,plain,(
% 1.17/0.52    ( ! [X2,X1] : (~m1_pre_topc(X2,sK0) | v1_tops_2(X1,X2) | ~r1_tarski(X1,u1_pre_topc(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) ) | ~spl3_1),
% 1.17/0.52    inference(resolution,[],[f139,f92])).
% 1.17/0.52  fof(f92,plain,(
% 1.17/0.52    ( ! [X0] : (m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK0)) )),
% 1.17/0.52    inference(resolution,[],[f76,f68])).
% 1.17/0.52  fof(f68,plain,(
% 1.17/0.52    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK1)) )),
% 1.17/0.52    inference(forward_demodulation,[],[f66,f29])).
% 1.17/0.52  fof(f29,plain,(
% 1.17/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 1.17/0.52    inference(cnf_transformation,[],[f15])).
% 1.17/0.52  fof(f66,plain,(
% 1.17/0.52    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X0,sK1)) )),
% 1.17/0.52    inference(resolution,[],[f47,f28])).
% 1.17/0.52  fof(f47,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f27])).
% 1.17/0.52  fof(f27,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f4])).
% 1.17/0.52  fof(f4,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.17/0.52  fof(f76,plain,(
% 1.17/0.52    ( ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X1,sK0)) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f73,f58])).
% 1.17/0.52  fof(f58,plain,(
% 1.17/0.52    ( ! [X1] : (~m1_pre_topc(X1,sK0) | l1_pre_topc(X1)) )),
% 1.17/0.52    inference(resolution,[],[f41,f32])).
% 1.17/0.52  fof(f41,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f21])).
% 1.17/0.52  fof(f21,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f2])).
% 1.17/0.52  fof(f2,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.17/0.52  fof(f73,plain,(
% 1.17/0.52    ( ! [X1] : (~l1_pre_topc(X1) | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X1,sK0)) )),
% 1.17/0.52    inference(resolution,[],[f40,f32])).
% 1.17/0.52  fof(f40,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f20])).
% 1.17/0.52  fof(f20,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f5])).
% 1.17/0.52  fof(f5,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.17/0.52  fof(f139,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(sK1))) ) | ~spl3_1),
% 1.17/0.52    inference(subsumption_resolution,[],[f138,f129])).
% 1.17/0.52  fof(f129,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) ) | ~spl3_1),
% 1.17/0.52    inference(forward_demodulation,[],[f127,f86])).
% 1.17/0.52  fof(f127,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) )),
% 1.17/0.52    inference(resolution,[],[f43,f28])).
% 1.17/0.52  fof(f43,plain,(
% 1.17/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f23])).
% 1.17/0.52  fof(f23,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f6])).
% 1.17/0.52  fof(f6,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).
% 1.17/0.52  fof(f138,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_1),
% 1.17/0.52    inference(resolution,[],[f136,f119])).
% 1.17/0.52  fof(f119,plain,(
% 1.17/0.52    ( ! [X0] : (v1_tops_2(X0,sK1) | ~r1_tarski(X0,u1_pre_topc(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_1),
% 1.17/0.52    inference(forward_demodulation,[],[f117,f86])).
% 1.17/0.52  fof(f117,plain,(
% 1.17/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~r1_tarski(X0,u1_pre_topc(sK1)) | v1_tops_2(X0,sK1)) )),
% 1.17/0.52    inference(resolution,[],[f44,f28])).
% 1.17/0.52  fof(f44,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f24])).
% 1.17/0.52  fof(f136,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~v1_tops_2(X1,sK1) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0)) )),
% 1.17/0.52    inference(resolution,[],[f54,f28])).
% 1.17/0.52  fof(f54,plain,(
% 1.17/0.52    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~v1_tops_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | v1_tops_2(X3,X2)) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f51,f43])).
% 1.17/0.52  fof(f51,plain,(
% 1.17/0.52    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X2,X0) | ~v1_tops_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | v1_tops_2(X3,X2)) )),
% 1.17/0.52    inference(equality_resolution,[],[f46])).
% 1.17/0.52  fof(f46,plain,(
% 1.17/0.52    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X2,X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | X1 != X3 | v1_tops_2(X3,X2)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f26])).
% 1.17/0.52  fof(f26,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(flattening,[],[f25])).
% 1.17/0.52  % (11040)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.17/0.52  fof(f25,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f7])).
% 1.17/0.52  fof(f7,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).
% 1.17/0.52  fof(f165,plain,(
% 1.17/0.52    spl3_3 | ~spl3_4 | ~spl3_1),
% 1.17/0.52    inference(avatar_split_clause,[],[f156,f84,f162,f158])).
% 1.17/0.52  fof(f156,plain,(
% 1.17/0.52    ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~spl3_1),
% 1.17/0.52    inference(resolution,[],[f155,f50])).
% 1.17/0.52  fof(f50,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.17/0.52    inference(cnf_transformation,[],[f1])).
% 1.17/0.52  fof(f155,plain,(
% 1.17/0.52    r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~spl3_1),
% 1.17/0.52    inference(subsumption_resolution,[],[f154,f32])).
% 1.17/0.52  fof(f154,plain,(
% 1.17/0.52    r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~l1_pre_topc(sK0) | ~spl3_1),
% 1.17/0.52    inference(subsumption_resolution,[],[f152,f52])).
% 1.17/0.52  fof(f152,plain,(
% 1.17/0.52    ~r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~l1_pre_topc(sK0) | ~spl3_1),
% 1.17/0.52    inference(resolution,[],[f150,f34])).
% 1.17/0.52  fof(f150,plain,(
% 1.17/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X2,u1_pre_topc(sK0)) | r1_tarski(X2,u1_pre_topc(sK1))) ) | ~spl3_1),
% 1.17/0.52    inference(duplicate_literal_removal,[],[f149])).
% 1.17/0.52  fof(f149,plain,(
% 1.17/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X2,u1_pre_topc(sK0)) | r1_tarski(X2,u1_pre_topc(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_1),
% 1.17/0.52    inference(resolution,[],[f147,f122])).
% 1.17/0.52  fof(f122,plain,(
% 1.17/0.52    ( ! [X0] : (~v1_tops_2(X0,sK1) | r1_tarski(X0,u1_pre_topc(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_1),
% 1.17/0.52    inference(forward_demodulation,[],[f120,f86])).
% 1.17/0.52  fof(f120,plain,(
% 1.17/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | r1_tarski(X0,u1_pre_topc(sK1)) | ~v1_tops_2(X0,sK1)) )),
% 1.17/0.52    inference(resolution,[],[f45,f28])).
% 1.17/0.52  fof(f147,plain,(
% 1.17/0.52    ( ! [X0] : (v1_tops_2(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,u1_pre_topc(sK0))) ) | ~spl3_1),
% 1.17/0.52    inference(forward_demodulation,[],[f145,f86])).
% 1.17/0.52  fof(f145,plain,(
% 1.17/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | v1_tops_2(X0,sK1) | ~r1_tarski(X0,u1_pre_topc(sK0))) )),
% 1.17/0.52    inference(resolution,[],[f141,f79])).
% 1.17/0.52  fof(f79,plain,(
% 1.17/0.52    m1_pre_topc(sK1,sK0)),
% 1.17/0.52    inference(resolution,[],[f78,f55])).
% 1.17/0.52  fof(f55,plain,(
% 1.17/0.52    m1_pre_topc(sK1,sK1)),
% 1.17/0.52    inference(resolution,[],[f33,f28])).
% 1.17/0.52  fof(f78,plain,(
% 1.17/0.52    ( ! [X1] : (~m1_pre_topc(X1,sK1) | m1_pre_topc(X1,sK0)) )),
% 1.17/0.52    inference(resolution,[],[f75,f67])).
% 1.17/0.52  fof(f67,plain,(
% 1.17/0.52    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X1,sK0)) )),
% 1.17/0.52    inference(resolution,[],[f47,f32])).
% 1.17/0.52  fof(f75,plain,(
% 1.17/0.52    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK1)) )),
% 1.17/0.52    inference(forward_demodulation,[],[f74,f29])).
% 1.17/0.52  fof(f74,plain,(
% 1.17/0.52    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK1)) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f72,f57])).
% 1.17/0.52  fof(f57,plain,(
% 1.17/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK1) | l1_pre_topc(X0)) )),
% 1.17/0.52    inference(resolution,[],[f41,f28])).
% 1.17/0.52  fof(f72,plain,(
% 1.17/0.52    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK1)) )),
% 1.17/0.52    inference(resolution,[],[f40,f28])).
% 1.17/0.52  fof(f141,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(sK0))) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f140,f128])).
% 1.17/0.52  fof(f128,plain,(
% 1.17/0.52    ( ! [X2,X3] : (~m1_pre_topc(X2,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.17/0.52    inference(resolution,[],[f43,f32])).
% 1.17/0.52  fof(f140,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.17/0.52    inference(resolution,[],[f137,f118])).
% 1.17/0.52  fof(f118,plain,(
% 1.17/0.52    ( ! [X1] : (v1_tops_2(X1,sK0) | ~r1_tarski(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.17/0.52    inference(resolution,[],[f44,f32])).
% 1.17/0.52  fof(f137,plain,(
% 1.17/0.52    ( ! [X2,X3] : (~v1_tops_2(X3,sK0) | ~m1_pre_topc(X2,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | v1_tops_2(X3,X2)) )),
% 1.17/0.52    inference(resolution,[],[f54,f32])).
% 1.17/0.52  fof(f100,plain,(
% 1.17/0.52    spl3_2),
% 1.17/0.52    inference(avatar_contradiction_clause,[],[f99])).
% 1.17/0.52  fof(f99,plain,(
% 1.17/0.52    $false | spl3_2),
% 1.17/0.52    inference(subsumption_resolution,[],[f98,f90])).
% 1.17/0.52  fof(f90,plain,(
% 1.17/0.52    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | spl3_2),
% 1.17/0.52    inference(avatar_component_clause,[],[f88])).
% 1.17/0.52  fof(f88,plain,(
% 1.17/0.52    spl3_2 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.17/0.52  fof(f98,plain,(
% 1.17/0.52    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.17/0.52    inference(resolution,[],[f95,f56])).
% 1.17/0.52  fof(f95,plain,(
% 1.17/0.52    ( ! [X1] : (~m1_pre_topc(X1,sK0) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK1))) )),
% 1.17/0.52    inference(resolution,[],[f92,f62])).
% 1.17/0.52  fof(f62,plain,(
% 1.17/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK1) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1))) )),
% 1.17/0.52    inference(resolution,[],[f42,f28])).
% 1.17/0.52  fof(f42,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f22])).
% 1.17/0.52  fof(f22,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f10])).
% 1.17/0.52  fof(f10,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 1.17/0.52  fof(f91,plain,(
% 1.17/0.52    spl3_1 | ~spl3_2),
% 1.17/0.52    inference(avatar_split_clause,[],[f82,f88,f84])).
% 1.17/0.52  fof(f82,plain,(
% 1.17/0.52    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK0) = u1_struct_0(sK1)),
% 1.17/0.52    inference(resolution,[],[f80,f50])).
% 1.17/0.52  fof(f80,plain,(
% 1.17/0.52    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.17/0.52    inference(resolution,[],[f79,f63])).
% 1.17/0.52  fof(f63,plain,(
% 1.17/0.52    ( ! [X1] : (~m1_pre_topc(X1,sK0) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK0))) )),
% 1.17/0.52    inference(resolution,[],[f42,f32])).
% 1.17/0.52  % SZS output end Proof for theBenchmark
% 1.17/0.52  % (11055)------------------------------
% 1.17/0.52  % (11055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (11055)Termination reason: Refutation
% 1.17/0.52  
% 1.17/0.52  % (11055)Memory used [KB]: 10746
% 1.17/0.52  % (11055)Time elapsed: 0.057 s
% 1.17/0.52  % (11055)------------------------------
% 1.17/0.52  % (11055)------------------------------
% 1.17/0.53  % (11033)Refutation not found, incomplete strategy% (11033)------------------------------
% 1.17/0.53  % (11033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.53  % (11033)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.53  
% 1.17/0.53  % (11033)Memory used [KB]: 10618
% 1.17/0.53  % (11033)Time elapsed: 0.086 s
% 1.17/0.53  % (11033)------------------------------
% 1.17/0.53  % (11033)------------------------------
% 1.17/0.53  % (11037)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.17/0.53  % (11032)Success in time 0.156 s
%------------------------------------------------------------------------------
