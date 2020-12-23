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
% DateTime   : Thu Dec  3 13:15:25 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 143 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  236 ( 396 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f99,f104,f109,f123,f143,f190,f198,f215,f219,f235])).

fof(f235,plain,
    ( spl6_17
    | ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl6_17
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f229,f197])).

fof(f197,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_17
  <=> r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f229,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl6_19 ),
    inference(resolution,[],[f214,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f214,plain,
    ( r2_hidden(sK5(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl6_19
  <=> r2_hidden(sK5(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f219,plain,
    ( ~ spl6_7
    | spl6_16 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl6_7
    | spl6_16 ),
    inference(subsumption_resolution,[],[f216,f122])).

fof(f122,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f216,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl6_16 ),
    inference(resolution,[],[f189,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f189,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl6_16
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f215,plain,
    ( spl6_19
    | spl6_17 ),
    inference(avatar_split_clause,[],[f200,f195,f212])).

fof(f200,plain,
    ( r2_hidden(sK5(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0))
    | spl6_17 ),
    inference(resolution,[],[f197,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f198,plain,
    ( ~ spl6_17
    | spl6_15 ),
    inference(avatar_split_clause,[],[f191,f183,f195])).

fof(f183,plain,
    ( spl6_15
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f191,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | spl6_15 ),
    inference(resolution,[],[f185,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f185,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f183])).

fof(f190,plain,
    ( ~ spl6_15
    | ~ spl6_16
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f155,f140,f120,f106,f101,f84,f79,f187,f183])).

fof(f79,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f84,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f101,plain,
    ( spl6_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f106,plain,
    ( spl6_6
  <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f140,plain,
    ( spl6_10
  <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f155,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f154,f142])).

fof(f142,plain,
    ( k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f154,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f151,f122])).

fof(f151,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_6 ),
    inference(resolution,[],[f118,f108])).

fof(f108,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( m2_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f116,f112])).

fof(f112,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f103,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f103,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f91,f112])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f88,f86])).

fof(f86,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f81,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f81,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f143,plain,
    ( spl6_10
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f93,f84,f79,f140])).

fof(f93,plain,
    ( k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f90,f86])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f81,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f123,plain,
    ( spl6_7
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f114,f101,f96,f120])).

fof(f96,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f114,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f98,f112])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f109,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f39,f106])).

fof(f39,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f104,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f94,f84,f101])).

fof(f94,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f99,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f38,f96])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f87,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f41,f79])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:51:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (15357)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.51  % (15348)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (15354)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.17/0.52  % (15342)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.52  % (15357)Refutation found. Thanks to Tanya!
% 1.17/0.52  % SZS status Theorem for theBenchmark
% 1.17/0.52  % SZS output start Proof for theBenchmark
% 1.17/0.52  fof(f236,plain,(
% 1.17/0.52    $false),
% 1.17/0.52    inference(avatar_sat_refutation,[],[f82,f87,f99,f104,f109,f123,f143,f190,f198,f215,f219,f235])).
% 1.17/0.52  fof(f235,plain,(
% 1.17/0.52    spl6_17 | ~spl6_19),
% 1.17/0.52    inference(avatar_contradiction_clause,[],[f234])).
% 1.17/0.52  fof(f234,plain,(
% 1.17/0.52    $false | (spl6_17 | ~spl6_19)),
% 1.17/0.52    inference(subsumption_resolution,[],[f229,f197])).
% 1.17/0.52  fof(f197,plain,(
% 1.17/0.52    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | spl6_17),
% 1.17/0.52    inference(avatar_component_clause,[],[f195])).
% 1.17/0.52  fof(f195,plain,(
% 1.17/0.52    spl6_17 <=> r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.17/0.52  fof(f229,plain,(
% 1.17/0.52    r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl6_19),
% 1.17/0.52    inference(resolution,[],[f214,f67])).
% 1.17/0.52  fof(f67,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f35])).
% 1.17/0.52  fof(f35,plain,(
% 1.17/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f2])).
% 1.17/0.52  fof(f2,axiom,(
% 1.17/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.17/0.52  fof(f214,plain,(
% 1.17/0.52    r2_hidden(sK5(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0)) | ~spl6_19),
% 1.17/0.52    inference(avatar_component_clause,[],[f212])).
% 1.17/0.52  fof(f212,plain,(
% 1.17/0.52    spl6_19 <=> r2_hidden(sK5(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0))),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.17/0.52  fof(f219,plain,(
% 1.17/0.52    ~spl6_7 | spl6_16),
% 1.17/0.52    inference(avatar_contradiction_clause,[],[f218])).
% 1.17/0.52  fof(f218,plain,(
% 1.17/0.52    $false | (~spl6_7 | spl6_16)),
% 1.17/0.52    inference(subsumption_resolution,[],[f216,f122])).
% 1.17/0.52  fof(f122,plain,(
% 1.17/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl6_7),
% 1.17/0.52    inference(avatar_component_clause,[],[f120])).
% 1.17/0.52  fof(f120,plain,(
% 1.17/0.52    spl6_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.17/0.52  fof(f216,plain,(
% 1.17/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl6_16),
% 1.17/0.52    inference(resolution,[],[f189,f69])).
% 1.17/0.52  fof(f69,plain,(
% 1.17/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f13])).
% 1.17/0.52  fof(f13,axiom,(
% 1.17/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.17/0.52  fof(f189,plain,(
% 1.17/0.52    ~r1_tarski(sK1,k2_struct_0(sK0)) | spl6_16),
% 1.17/0.52    inference(avatar_component_clause,[],[f187])).
% 1.17/0.52  fof(f187,plain,(
% 1.17/0.52    spl6_16 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.17/0.52  fof(f215,plain,(
% 1.17/0.52    spl6_19 | spl6_17),
% 1.17/0.52    inference(avatar_split_clause,[],[f200,f195,f212])).
% 1.17/0.52  fof(f200,plain,(
% 1.17/0.52    r2_hidden(sK5(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0)) | spl6_17),
% 1.17/0.52    inference(resolution,[],[f197,f66])).
% 1.17/0.52  fof(f66,plain,(
% 1.17/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f35])).
% 1.17/0.52  fof(f198,plain,(
% 1.17/0.52    ~spl6_17 | spl6_15),
% 1.17/0.52    inference(avatar_split_clause,[],[f191,f183,f195])).
% 1.17/0.52  fof(f183,plain,(
% 1.17/0.52    spl6_15 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.17/0.52  fof(f191,plain,(
% 1.17/0.52    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | spl6_15),
% 1.17/0.52    inference(resolution,[],[f185,f68])).
% 1.17/0.52  fof(f68,plain,(
% 1.17/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f13])).
% 1.17/0.52  fof(f185,plain,(
% 1.17/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl6_15),
% 1.17/0.52    inference(avatar_component_clause,[],[f183])).
% 1.17/0.52  fof(f190,plain,(
% 1.17/0.52    ~spl6_15 | ~spl6_16 | ~spl6_2 | ~spl6_3 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_10),
% 1.17/0.52    inference(avatar_split_clause,[],[f155,f140,f120,f106,f101,f84,f79,f187,f183])).
% 1.17/0.52  fof(f79,plain,(
% 1.17/0.52    spl6_2 <=> v2_pre_topc(sK0)),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.17/0.52  fof(f84,plain,(
% 1.17/0.52    spl6_3 <=> l1_pre_topc(sK0)),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.17/0.52  fof(f101,plain,(
% 1.17/0.52    spl6_5 <=> l1_struct_0(sK0)),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.17/0.52  fof(f106,plain,(
% 1.17/0.52    spl6_6 <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.17/0.52  fof(f140,plain,(
% 1.17/0.52    spl6_10 <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.17/0.52  fof(f155,plain,(
% 1.17/0.52    ~r1_tarski(sK1,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_10)),
% 1.17/0.52    inference(forward_demodulation,[],[f154,f142])).
% 1.17/0.52  fof(f142,plain,(
% 1.17/0.52    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | ~spl6_10),
% 1.17/0.52    inference(avatar_component_clause,[],[f140])).
% 1.17/0.52  fof(f154,plain,(
% 1.17/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_5 | spl6_6 | ~spl6_7)),
% 1.17/0.52    inference(subsumption_resolution,[],[f151,f122])).
% 1.17/0.52  fof(f151,plain,(
% 1.17/0.52    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_5 | spl6_6)),
% 1.17/0.52    inference(resolution,[],[f118,f108])).
% 1.17/0.52  fof(f108,plain,(
% 1.17/0.52    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | spl6_6),
% 1.17/0.52    inference(avatar_component_clause,[],[f106])).
% 1.17/0.52  fof(f118,plain,(
% 1.17/0.52    ( ! [X0,X1] : (m2_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.17/0.52    inference(forward_demodulation,[],[f116,f112])).
% 1.17/0.52  fof(f112,plain,(
% 1.17/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl6_5),
% 1.17/0.52    inference(resolution,[],[f103,f47])).
% 1.17/0.52  fof(f47,plain,(
% 1.17/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f24])).
% 1.17/0.52  fof(f24,plain,(
% 1.17/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f14])).
% 1.17/0.52  fof(f14,axiom,(
% 1.17/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.17/0.52  fof(f103,plain,(
% 1.17/0.52    l1_struct_0(sK0) | ~spl6_5),
% 1.17/0.52    inference(avatar_component_clause,[],[f101])).
% 1.17/0.52  fof(f116,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.17/0.52    inference(backward_demodulation,[],[f91,f112])).
% 1.17/0.52  fof(f91,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | (~spl6_2 | ~spl6_3)),
% 1.17/0.52    inference(subsumption_resolution,[],[f88,f86])).
% 1.17/0.52  fof(f86,plain,(
% 1.17/0.52    l1_pre_topc(sK0) | ~spl6_3),
% 1.17/0.52    inference(avatar_component_clause,[],[f84])).
% 1.17/0.52  fof(f88,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | ~spl6_2),
% 1.17/0.52    inference(resolution,[],[f81,f53])).
% 1.17/0.52  fof(f53,plain,(
% 1.17/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f31])).
% 1.17/0.52  fof(f31,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.17/0.52    inference(flattening,[],[f30])).
% 1.17/0.52  fof(f30,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f17])).
% 1.17/0.52  fof(f17,axiom,(
% 1.17/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 1.17/0.52  fof(f81,plain,(
% 1.17/0.52    v2_pre_topc(sK0) | ~spl6_2),
% 1.17/0.52    inference(avatar_component_clause,[],[f79])).
% 1.17/0.52  fof(f143,plain,(
% 1.17/0.52    spl6_10 | ~spl6_2 | ~spl6_3),
% 1.17/0.52    inference(avatar_split_clause,[],[f93,f84,f79,f140])).
% 1.17/0.52  fof(f93,plain,(
% 1.17/0.52    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | (~spl6_2 | ~spl6_3)),
% 1.17/0.52    inference(subsumption_resolution,[],[f90,f86])).
% 1.17/0.52  fof(f90,plain,(
% 1.17/0.52    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | ~spl6_2),
% 1.17/0.52    inference(resolution,[],[f81,f52])).
% 1.17/0.52  fof(f52,plain,(
% 1.17/0.52    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f29])).
% 1.17/0.52  fof(f29,plain,(
% 1.17/0.52    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.17/0.52    inference(flattening,[],[f28])).
% 1.17/0.52  fof(f28,plain,(
% 1.17/0.52    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f16])).
% 1.17/0.52  fof(f16,axiom,(
% 1.17/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 1.17/0.52  fof(f123,plain,(
% 1.17/0.52    spl6_7 | ~spl6_4 | ~spl6_5),
% 1.17/0.52    inference(avatar_split_clause,[],[f114,f101,f96,f120])).
% 1.17/0.52  fof(f96,plain,(
% 1.17/0.52    spl6_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.17/0.52  fof(f114,plain,(
% 1.17/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl6_4 | ~spl6_5)),
% 1.17/0.52    inference(backward_demodulation,[],[f98,f112])).
% 1.17/0.52  fof(f98,plain,(
% 1.17/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_4),
% 1.17/0.52    inference(avatar_component_clause,[],[f96])).
% 1.17/0.52  fof(f109,plain,(
% 1.17/0.52    ~spl6_6),
% 1.17/0.52    inference(avatar_split_clause,[],[f39,f106])).
% 1.17/0.52  fof(f39,plain,(
% 1.17/0.52    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 1.17/0.52    inference(cnf_transformation,[],[f23])).
% 1.17/0.52  fof(f23,plain,(
% 1.17/0.52    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/0.52    inference(flattening,[],[f22])).
% 1.17/0.52  fof(f22,plain,(
% 1.17/0.52    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f20])).
% 1.17/0.52  fof(f20,negated_conjecture,(
% 1.17/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.17/0.52    inference(negated_conjecture,[],[f19])).
% 1.17/0.52  fof(f19,conjecture,(
% 1.17/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 1.17/0.52  fof(f104,plain,(
% 1.17/0.52    spl6_5 | ~spl6_3),
% 1.17/0.52    inference(avatar_split_clause,[],[f94,f84,f101])).
% 1.17/0.52  fof(f94,plain,(
% 1.17/0.52    l1_struct_0(sK0) | ~spl6_3),
% 1.17/0.52    inference(resolution,[],[f86,f48])).
% 1.17/0.52  fof(f48,plain,(
% 1.17/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f25])).
% 1.17/0.52  fof(f25,plain,(
% 1.17/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f15])).
% 1.17/0.52  fof(f15,axiom,(
% 1.17/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.17/0.52  fof(f99,plain,(
% 1.17/0.52    spl6_4),
% 1.17/0.52    inference(avatar_split_clause,[],[f38,f96])).
% 1.17/0.52  fof(f38,plain,(
% 1.17/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.17/0.52    inference(cnf_transformation,[],[f23])).
% 1.17/0.52  fof(f87,plain,(
% 1.17/0.52    spl6_3),
% 1.17/0.52    inference(avatar_split_clause,[],[f42,f84])).
% 1.17/0.52  fof(f42,plain,(
% 1.17/0.52    l1_pre_topc(sK0)),
% 1.17/0.52    inference(cnf_transformation,[],[f23])).
% 1.17/0.52  fof(f82,plain,(
% 1.17/0.52    spl6_2),
% 1.17/0.52    inference(avatar_split_clause,[],[f41,f79])).
% 1.17/0.52  fof(f41,plain,(
% 1.17/0.52    v2_pre_topc(sK0)),
% 1.17/0.52    inference(cnf_transformation,[],[f23])).
% 1.17/0.52  % SZS output end Proof for theBenchmark
% 1.17/0.52  % (15357)------------------------------
% 1.17/0.52  % (15357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (15357)Termination reason: Refutation
% 1.17/0.52  
% 1.17/0.52  % (15357)Memory used [KB]: 10874
% 1.17/0.52  % (15357)Time elapsed: 0.113 s
% 1.17/0.52  % (15357)------------------------------
% 1.17/0.52  % (15357)------------------------------
% 1.17/0.52  % (15339)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.17/0.52  % (15336)Success in time 0.158 s
%------------------------------------------------------------------------------
