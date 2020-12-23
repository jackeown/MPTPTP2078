%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1578+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 474 expanded)
%              Number of leaves         :   25 ( 146 expanded)
%              Depth                    :   23
%              Number of atoms          :  481 (1470 expanded)
%              Number of equality atoms :   61 ( 213 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f94,f98,f103,f116,f204,f211,f278,f283,f286,f299])).

fof(f299,plain,
    ( spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f297,f276])).

fof(f276,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl2_13
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f297,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f296,f203])).

fof(f203,plain,
    ( ! [X0] : u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X0
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl2_11
  <=> ! [X0] : u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f296,plain,
    ( ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f295,f220])).

fof(f220,plain,
    ( ! [X0] : r1_tarski(k1_toler_1(u1_orders_2(sK0),X0),u1_orders_2(sK0))
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f219,f199])).

fof(f199,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl2_10
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f219,plain,
    ( ! [X0] :
        ( r1_tarski(k1_toler_1(u1_orders_2(sK0),X0),u1_orders_2(sK0))
        | ~ v1_relat_1(u1_orders_2(sK0)) )
    | ~ spl2_10 ),
    inference(superposition,[],[f218,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k1_toler_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k1_toler_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,X1) = k1_toler_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_toler_1)).

fof(f218,plain,
    ( ! [X1] : r1_tarski(k2_wellord1(u1_orders_2(sK0),X1),u1_orders_2(sK0))
    | ~ spl2_10 ),
    inference(superposition,[],[f45,f213])).

fof(f213,plain,
    ( ! [X1] : k2_wellord1(u1_orders_2(sK0),X1) = k3_xboole_0(u1_orders_2(sK0),k2_zfmisc_1(X1,X1))
    | ~ spl2_10 ),
    inference(resolution,[],[f199,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f295,plain,
    ( ~ r1_tarski(k1_toler_1(u1_orders_2(sK0),sK1),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f294,f246])).

fof(f246,plain,
    ( ! [X0] : k1_toler_1(u1_orders_2(sK0),X0) = u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f244,f199])).

fof(f244,plain,
    ( ! [X0] :
        ( k1_toler_1(u1_orders_2(sK0),X0) = u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)))
        | ~ v1_relat_1(u1_orders_2(sK0)) )
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(resolution,[],[f243,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_toler_1)).

fof(f243,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_toler_1(u1_orders_2(sK0),X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | k1_toler_1(u1_orders_2(sK0),X0) = u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) )
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(equality_resolution,[],[f186])).

fof(f186,plain,
    ( ! [X12,X13,X11] :
        ( g1_orders_2(X11,k1_toler_1(u1_orders_2(sK0),X11)) != g1_orders_2(X12,X13)
        | u1_orders_2(g1_orders_2(X11,k1_toler_1(u1_orders_2(sK0),X11))) = X13
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))) )
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f51,f179])).

fof(f179,plain,
    ( ! [X6] : g1_orders_2(X6,k1_toler_1(u1_orders_2(sK0),X6)) = g1_orders_2(u1_struct_0(g1_orders_2(X6,k1_toler_1(u1_orders_2(sK0),X6))),u1_orders_2(g1_orders_2(X6,k1_toler_1(u1_orders_2(sK0),X6))))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(resolution,[],[f111,f150])).

fof(f150,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f149,f121])).

fof(f121,plain,
    ( u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl2_4 ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X3 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_4
  <=> ! [X3,X2] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f149,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f147,f102])).

fof(f102,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl2_6
  <=> l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f147,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl2_5 ),
    inference(superposition,[],[f38,f145])).

fof(f145,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl2_5 ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,
    ( ! [X6,X7] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X6,X7)
        | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X6 )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_5
  <=> ! [X7,X6] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X6,X7)
        | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | g1_orders_2(X0,k1_toler_1(X1,X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_toler_1(X1,X0))),u1_orders_2(g1_orders_2(X0,k1_toler_1(X1,X0)))) ) ),
    inference(resolution,[],[f74,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f74,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X4)
      | g1_orders_2(X3,k1_toler_1(X4,X3)) = g1_orders_2(u1_struct_0(g1_orders_2(X3,k1_toler_1(X4,X3))),u1_orders_2(g1_orders_2(X3,k1_toler_1(X4,X3)))) ) ),
    inference(resolution,[],[f66,f47])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) = g1_orders_2(u1_struct_0(g1_orders_2(X0,X1)),u1_orders_2(g1_orders_2(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f65,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f24])).

% (867)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (870)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (869)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (864)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (864)Refutation not found, incomplete strategy% (864)------------------------------
% (864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (864)Termination reason: Refutation not found, incomplete strategy

% (864)Memory used [KB]: 1663
% (864)Time elapsed: 0.140 s
% (864)------------------------------
% (864)------------------------------
% (865)Refutation not found, incomplete strategy% (865)------------------------------
% (865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (865)Termination reason: Refutation not found, incomplete strategy

% (865)Memory used [KB]: 10746
% (865)Time elapsed: 0.140 s
% (865)------------------------------
% (865)------------------------------
% (852)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (862)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (851)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (859)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (852)Refutation not found, incomplete strategy% (852)------------------------------
% (852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (861)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (852)Termination reason: Refutation not found, incomplete strategy

% (852)Memory used [KB]: 10618
% (852)Time elapsed: 0.135 s
% (852)------------------------------
% (852)------------------------------
% (850)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (856)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (853)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (863)Refutation not found, incomplete strategy% (863)------------------------------
% (863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (863)Termination reason: Refutation not found, incomplete strategy

% (863)Memory used [KB]: 10746
% (863)Time elapsed: 0.154 s
% (863)------------------------------
% (863)------------------------------
% (853)Refutation not found, incomplete strategy% (853)------------------------------
% (853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (853)Termination reason: Refutation not found, incomplete strategy

% (853)Memory used [KB]: 10746
% (853)Time elapsed: 0.153 s
% (853)------------------------------
% (853)------------------------------
fof(f24,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(f65,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) = g1_orders_2(u1_struct_0(g1_orders_2(X0,X1)),u1_orders_2(g1_orders_2(X0,X1)))
      | ~ l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f294,plain,
    ( ~ r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | spl2_2
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f293,f34])).

fof(f34,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
      | ~ v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
              | ~ v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(sK0),X1)),sK0)
            | ~ v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(sK0),X1)),sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ( ~ m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(sK0),X1)),sK0)
          | ~ v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(sK0),X1)),sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
        | ~ v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
            | ~ v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
              & v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
            & v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_yellow_0)).

fof(f293,plain,
    ( ~ r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl2_2
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f292,f272])).

fof(f272,plain,
    ( l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl2_12
  <=> l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f292,plain,
    ( ~ r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | ~ l1_orders_2(sK0)
    | spl2_2 ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_yellow_0(X1,X0)
      | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f62,plain,
    ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_2
  <=> m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f286,plain,(
    spl2_13 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl2_13 ),
    inference(subsumption_resolution,[],[f284,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f284,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_13 ),
    inference(resolution,[],[f277,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f277,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f275])).

fof(f283,plain,
    ( ~ spl2_10
    | spl2_12 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl2_10
    | spl2_12 ),
    inference(subsumption_resolution,[],[f280,f199])).

fof(f280,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | spl2_12 ),
    inference(resolution,[],[f279,f47])).

fof(f279,plain,
    ( ~ m1_subset_1(k1_toler_1(u1_orders_2(sK0),sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | spl2_12 ),
    inference(resolution,[],[f273,f49])).

fof(f273,plain,
    ( ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f271])).

fof(f278,plain,
    ( ~ spl2_12
    | ~ spl2_13
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f269,f202,f198,f100,f96,f92,f56,f275,f271])).

fof(f56,plain,
    ( spl2_1
  <=> v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f269,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f268,f203])).

fof(f268,plain,
    ( ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f267,f220])).

fof(f267,plain,
    ( ~ r1_tarski(k1_toler_1(u1_orders_2(sK0),sK1),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f266,f246])).

fof(f266,plain,
    ( ~ r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f265,f34])).

fof(f265,plain,
    ( ~ r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | ~ l1_orders_2(sK0)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(resolution,[],[f264,f42])).

fof(f264,plain,
    ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f263,f34])).

fof(f263,plain,
    ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | ~ l1_orders_2(sK0)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(trivial_inequality_removal,[],[f262])).

fof(f262,plain,
    ( k1_toler_1(u1_orders_2(sK0),sK1) != k1_toler_1(u1_orders_2(sK0),sK1)
    | ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | ~ l1_orders_2(sK0)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(resolution,[],[f261,f58])).

fof(f58,plain,
    ( ~ v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f261,plain,
    ( ! [X0,X1] :
        ( v4_yellow_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)),X1)
        | k1_toler_1(u1_orders_2(sK0),X0) != k1_toler_1(u1_orders_2(X1),X0)
        | ~ m1_yellow_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)),X1)
        | ~ l1_orders_2(X1) )
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f216,f246])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) != k1_toler_1(u1_orders_2(X1),X0)
        | v4_yellow_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)),X1)
        | ~ m1_yellow_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)),X1)
        | ~ l1_orders_2(X1) )
    | ~ spl2_11 ),
    inference(superposition,[],[f44,f203])).

fof(f44,plain,(
    ! [X0,X1] :
      ( u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
      | v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_yellow_0(X1,X0)
              | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
            & ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
              | ~ v4_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_yellow_0)).

fof(f211,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl2_10 ),
    inference(subsumption_resolution,[],[f207,f34])).

fof(f207,plain,
    ( ~ l1_orders_2(sK0)
    | spl2_10 ),
    inference(resolution,[],[f205,f38])).

fof(f205,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl2_10 ),
    inference(resolution,[],[f200,f54])).

fof(f200,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f204,plain,
    ( ~ spl2_10
    | spl2_11
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f195,f100,f96,f92,f202,f198])).

fof(f195,plain,
    ( ! [X0] :
        ( u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X0
        | ~ v1_relat_1(u1_orders_2(sK0)) )
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(resolution,[],[f194,f47])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_toler_1(u1_orders_2(sK0),X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X0 )
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(equality_resolution,[],[f184])).

fof(f184,plain,
    ( ! [X6,X7,X5] :
        ( g1_orders_2(X6,X7) != g1_orders_2(X5,k1_toler_1(u1_orders_2(sK0),X5))
        | u1_struct_0(g1_orders_2(X5,k1_toler_1(u1_orders_2(sK0),X5))) = X6
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) )
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f50,f179])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f116,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f113,f34])).

fof(f113,plain,
    ( ~ l1_orders_2(sK0)
    | spl2_3 ),
    inference(resolution,[],[f112,f38])).

fof(f112,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl2_3 ),
    inference(resolution,[],[f109,f49])).

fof(f109,plain,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | spl2_3 ),
    inference(resolution,[],[f90,f38])).

fof(f90,plain,
    ( ~ m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_3
  <=> m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f103,plain,
    ( ~ spl2_3
    | spl2_6 ),
    inference(avatar_split_clause,[],[f85,f100,f88])).

fof(f85,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) ),
    inference(superposition,[],[f49,f79])).

fof(f79,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    inference(resolution,[],[f73,f34])).

fof(f73,plain,(
    ! [X2] :
      ( ~ l1_orders_2(X2)
      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))),u1_orders_2(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) ) ),
    inference(resolution,[],[f66,f38])).

fof(f98,plain,
    ( ~ spl2_3
    | spl2_5 ),
    inference(avatar_split_clause,[],[f84,f96,f88])).

fof(f84,plain,(
    ! [X6,X7] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X6,X7)
      | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X6
      | ~ m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) ) ),
    inference(superposition,[],[f50,f79])).

fof(f94,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f82,f92,f88])).

fof(f82,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X3
      | ~ m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))))) ) ),
    inference(superposition,[],[f51,f79])).

fof(f63,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f36,f60,f56])).

fof(f36,plain,
    ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | ~ v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
