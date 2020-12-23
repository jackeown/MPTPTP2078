%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  88 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   15
%              Number of atoms          :  176 ( 385 expanded)
%              Number of equality atoms :   10 (  43 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f368,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f298,f367])).

fof(f367,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f365,f103])).

fof(f103,plain,(
    ~ m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f102,f14])).

fof(f14,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tsep_1(X0,X1,X1) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tsep_1(X0,X1,X1) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f102,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f101,f13])).

fof(f13,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f101,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f100,f18])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f99,f17])).

fof(f17,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f99,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f98,f16])).

fof(f16,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f98,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f27,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | sQ3_eqProxy(k1_tsep_1(X0,X1,X2),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_pre_topc(X1,X2) ) ),
    inference(equality_proxy_replacement,[],[f20,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

fof(f27,plain,(
    ~ sQ3_eqProxy(k1_tsep_1(sK0,sK1,sK1),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(equality_proxy_replacement,[],[f15,f26])).

fof(f15,plain,(
    k1_tsep_1(sK0,sK1,sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f365,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f354,f14])).

fof(f354,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | m1_pre_topc(sK1,sK1)
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f350])).

fof(f350,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f241,f54])).

fof(f54,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
      | ~ m1_pre_topc(X3,sK0)
      | m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f50,f18])).

fof(f50,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X3,sK0)
      | m1_pre_topc(X2,X3)
      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f17,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

% (15656)Termination reason: Refutation not found, incomplete strategy

% (15656)Memory used [KB]: 1663
fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

% (15656)Time elapsed: 0.063 s
% (15656)------------------------------
% (15656)------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f241,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl4_3
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f298,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f294,f293])).

fof(f293,plain,
    ( r2_hidden(sK2(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl4_3 ),
    inference(resolution,[],[f242,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f242,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f240])).

fof(f294,plain,
    ( ~ r2_hidden(sK2(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl4_3 ),
    inference(resolution,[],[f242,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:05:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (15648)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.47  % (15648)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (15656)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.47  % (15656)Refutation not found, incomplete strategy% (15656)------------------------------
% 0.21/0.47  % (15656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f368,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f298,f367])).
% 0.21/0.47  fof(f367,plain,(
% 0.21/0.47    ~spl4_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f366])).
% 0.21/0.47  fof(f366,plain,(
% 0.21/0.47    $false | ~spl4_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f365,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f102,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    m1_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (k1_tsep_1(X0,X1,X1) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (k1_tsep_1(X0,X1,X1) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f101,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ~v2_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f100,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f99,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f98,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,sK1)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f95])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,sK1)),
% 0.21/0.47    inference(resolution,[],[f27,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | sQ3_eqProxy(k1_tsep_1(X0,X1,X2),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X1,X2)) )),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f20,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~sQ3_eqProxy(k1_tsep_1(sK0,sK1,sK1),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f15,f26])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    k1_tsep_1(sK0,sK1,sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f365,plain,(
% 0.21/0.47    m1_pre_topc(sK1,sK1) | ~spl4_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f354,f14])).
% 0.21/0.47  fof(f354,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | m1_pre_topc(sK1,sK1) | ~spl4_3),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f350])).
% 0.21/0.47  fof(f350,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK1,sK0) | ~spl4_3),
% 0.21/0.47    inference(resolution,[],[f241,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~r1_tarski(u1_struct_0(X2),u1_struct_0(X3)) | ~m1_pre_topc(X3,sK0) | m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f50,f18])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X3,sK0) | m1_pre_topc(X2,X3) | ~r1_tarski(u1_struct_0(X2),u1_struct_0(X3))) )),
% 0.21/0.47    inference(resolution,[],[f17,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  % (15656)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (15656)Memory used [KB]: 1663
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  % (15656)Time elapsed: 0.063 s
% 0.21/0.47  % (15656)------------------------------
% 0.21/0.47  % (15656)------------------------------
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f240])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    spl4_3 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f298,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f297])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    $false | spl4_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f294,f293])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    r2_hidden(sK2(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)) | spl4_3),
% 0.21/0.48    inference(resolution,[],[f242,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) | spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f240])).
% 0.21/0.48  fof(f294,plain,(
% 0.21/0.48    ~r2_hidden(sK2(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)) | spl4_3),
% 0.21/0.48    inference(resolution,[],[f242,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (15648)------------------------------
% 0.21/0.48  % (15648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15648)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (15648)Memory used [KB]: 6268
% 0.21/0.48  % (15648)Time elapsed: 0.058 s
% 0.21/0.48  % (15648)------------------------------
% 0.21/0.48  % (15648)------------------------------
% 0.21/0.48  % (15634)Success in time 0.126 s
%------------------------------------------------------------------------------
