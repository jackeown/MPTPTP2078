%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 390 expanded)
%              Number of leaves         :   16 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          :  343 (1604 expanded)
%              Number of equality atoms :   32 (  79 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f68,f99,f157,f159,f167,f212])).

fof(f212,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f211])).

% (25524)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (25528)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (25526)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (25550)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (25525)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (25524)Refutation not found, incomplete strategy% (25524)------------------------------
% (25524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25524)Termination reason: Refutation not found, incomplete strategy

% (25524)Memory used [KB]: 10618
% (25524)Time elapsed: 0.101 s
% (25524)------------------------------
% (25524)------------------------------
% (25533)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (25549)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (25537)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (25546)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f211,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(global_subsumption,[],[f190,f201,f208])).

fof(f208,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f207,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f207,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f205,f32])).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f205,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | r2_hidden(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f203,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f203,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f202,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f35,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f202,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f181,f62])).

fof(f62,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f181,plain,
    ( ! [X0] :
        ( v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(sK1)) )
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f176,f84])).

fof(f84,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_3
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v3_tex_2(X0,sK0)
        | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f126,f84])).

fof(f126,plain,(
    ! [X0] :
      ( v3_tex_2(X0,sK0)
      | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f125,f112])).

fof(f112,plain,(
    ! [X0] :
      ( v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f111,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f111,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f110,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f71,f30])).

fof(f30,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f43,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f37,f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f201,plain,
    ( sK1 != sK2(sK0,sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f200,f70])).

fof(f200,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | sK1 != sK2(sK0,sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f175,f62])).

fof(f175,plain,
    ( ! [X0] :
        ( v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | sK2(sK0,X0) != X0 )
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f124,f84])).

fof(f124,plain,(
    ! [X0] :
      ( v3_tex_2(X0,sK0)
      | sK2(sK0,X0) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f123,f112])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | sK2(sK0,X0) != X0
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f40,f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | sK2(X0,X1) != X1
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f190,plain,
    ( ~ r1_tarski(sK2(sK0,sK1),sK1)
    | sK1 = sK2(sK0,sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f189,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f189,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f188,f70])).

fof(f188,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | r1_tarski(sK1,sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f174,f62])).

fof(f174,plain,
    ( ! [X0] :
        ( v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | r1_tarski(X0,sK2(sK0,X0)) )
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f122,f84])).

fof(f122,plain,(
    ! [X0] :
      ( v3_tex_2(X0,sK0)
      | r1_tarski(X0,sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f121,f112])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | r1_tarski(X0,sK2(sK0,X0))
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f39,f31])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f167,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f101,f86,f82])).

fof(f86,plain,
    ( spl4_4
  <=> r1_tarski(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f101,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f78,f49])).

fof(f78,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f76,f57])).

fof(f76,plain,(
    r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f74,f32])).

fof(f74,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f44,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f159,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f144,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f144,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl4_1
    | spl4_4 ),
    inference(backward_demodulation,[],[f88,f139])).

fof(f139,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f137,f78])).

fof(f137,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f136,f70])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | sK1 = X0 )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f129,f27])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | sK1 = X0
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f128,f61])).

fof(f61,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f127,f112])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f41,f31])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f157,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f141,f69])).

fof(f69,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f33,f34])).

fof(f33,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f141,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f66,f139])).

fof(f66,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f99,plain,
    ( spl4_2
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f93,f55])).

fof(f93,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_2
    | spl4_4 ),
    inference(backward_demodulation,[],[f88,f92])).

fof(f92,plain,
    ( sK1 = u1_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f91,f65])).

fof(f65,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f91,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f45,f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f68,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f25,f64,f60])).

fof(f25,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f26,f64,f60])).

fof(f26,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:50:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (25531)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.48  % (25539)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (25531)Refutation not found, incomplete strategy% (25531)------------------------------
% 0.22/0.49  % (25531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25531)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25531)Memory used [KB]: 10618
% 0.22/0.49  % (25531)Time elapsed: 0.072 s
% 0.22/0.49  % (25531)------------------------------
% 0.22/0.49  % (25531)------------------------------
% 0.22/0.50  % (25529)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (25548)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (25548)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f67,f68,f99,f157,f159,f167,f212])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    spl4_1 | ~spl4_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f211])).
% 0.22/0.52  % (25524)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (25528)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (25526)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (25550)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (25525)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (25524)Refutation not found, incomplete strategy% (25524)------------------------------
% 0.22/0.52  % (25524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25524)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25524)Memory used [KB]: 10618
% 0.22/0.52  % (25524)Time elapsed: 0.101 s
% 0.22/0.52  % (25524)------------------------------
% 0.22/0.52  % (25524)------------------------------
% 0.22/0.52  % (25533)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (25549)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (25537)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (25546)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    $false | (spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(global_subsumption,[],[f190,f201,f208])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    r1_tarski(sK2(sK0,sK1),sK1) | (spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(resolution,[],[f207,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    r2_hidden(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | (spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f205,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    v1_xboole_0(k1_zfmisc_1(sK1)) | r2_hidden(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | (spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(resolution,[],[f203,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | (spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f202,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f35,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | (spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(resolution,[],[f181,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ~v3_tex_2(sK1,sK0) | spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    spl4_1 <=> v3_tex_2(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ( ! [X0] : (v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(sK1))) ) | ~spl4_3),
% 0.22/0.53    inference(forward_demodulation,[],[f176,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    sK1 = u1_struct_0(sK0) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl4_3 <=> sK1 = u1_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v3_tex_2(X0,sK0) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_3),
% 0.22/0.53    inference(backward_demodulation,[],[f126,f84])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ( ! [X0] : (v3_tex_2(X0,sK0) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f125,f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X0] : (v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f111,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f110,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f71,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    v1_tdlat_3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f43,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f37,f31])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    sK1 != sK2(sK0,sK1) | (spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f200,f70])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | sK1 != sK2(sK0,sK1) | (spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(resolution,[],[f175,f62])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ( ! [X0] : (v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | sK2(sK0,X0) != X0) ) | ~spl4_3),
% 0.22/0.53    inference(backward_demodulation,[],[f124,f84])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X0] : (v3_tex_2(X0,sK0) | sK2(sK0,X0) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f123,f112])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | sK2(sK0,X0) != X0 | v3_tex_2(X0,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f40,f31])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | sK2(X0,X1) != X1 | v3_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    ~r1_tarski(sK2(sK0,sK1),sK1) | sK1 = sK2(sK0,sK1) | (spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(resolution,[],[f189,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2(sK0,sK1)) | (spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f188,f70])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | r1_tarski(sK1,sK2(sK0,sK1)) | (spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(resolution,[],[f174,f62])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ( ! [X0] : (v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | r1_tarski(X0,sK2(sK0,X0))) ) | ~spl4_3),
% 0.22/0.53    inference(backward_demodulation,[],[f122,f84])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ( ! [X0] : (v3_tex_2(X0,sK0) | r1_tarski(X0,sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f121,f112])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | r1_tarski(X0,sK2(sK0,X0)) | v3_tex_2(X0,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f39,f31])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | v3_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    spl4_3 | ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f101,f86,f82])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl4_4 <=> r1_tarski(u1_struct_0(sK0),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ~r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f78,f49])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.53    inference(resolution,[],[f76,f57])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f74,f32])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(resolution,[],[f44,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ~spl4_1 | spl4_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f158])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    $false | (~spl4_1 | spl4_4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f144,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    ~r1_tarski(sK1,sK1) | (~spl4_1 | spl4_4)),
% 0.22/0.53    inference(backward_demodulation,[],[f88,f139])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    sK1 = u1_struct_0(sK0) | ~spl4_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f137,f78])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    ~r1_tarski(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~spl4_1),
% 0.22/0.53    inference(resolution,[],[f136,f70])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | sK1 = X0) ) | ~spl4_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f129,f27])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | sK1 = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_1),
% 0.22/0.53    inference(resolution,[],[f128,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    v3_tex_2(sK1,sK0) | ~spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f60])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v3_tex_2(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | X0 = X1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f127,f112])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~r1_tarski(X0,X1) | X0 = X1 | ~v3_tex_2(X0,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f41,f31])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~r1_tarski(X1,X2) | X1 = X2 | ~v3_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ~r1_tarski(u1_struct_0(sK0),sK1) | spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f86])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ~spl4_1 | ~spl4_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    $false | (~spl4_1 | ~spl4_2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f141,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.22/0.53    inference(backward_demodulation,[],[f33,f34])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    v1_subset_1(sK1,sK1) | (~spl4_1 | ~spl4_2)),
% 0.22/0.53    inference(backward_demodulation,[],[f66,f139])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    spl4_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl4_2 | spl4_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    $false | (spl4_2 | spl4_4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f93,f55])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ~r1_tarski(sK1,sK1) | (spl4_2 | spl4_4)),
% 0.22/0.53    inference(backward_demodulation,[],[f88,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    sK1 = u1_struct_0(sK0) | spl4_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f91,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f64])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    sK1 = u1_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    inference(resolution,[],[f45,f27])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    spl4_1 | ~spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f25,f64,f60])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ~spl4_1 | spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f64,f60])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (25548)------------------------------
% 0.22/0.53  % (25548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25548)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (25548)Memory used [KB]: 10746
% 0.22/0.53  % (25548)Time elapsed: 0.107 s
% 0.22/0.53  % (25548)------------------------------
% 0.22/0.53  % (25548)------------------------------
% 0.22/0.53  % (25540)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (25521)Success in time 0.169 s
%------------------------------------------------------------------------------
