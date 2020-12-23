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
% DateTime   : Thu Dec  3 13:22:41 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 113 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  216 ( 397 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f95,f98,f119,f141,f195,f198])).

fof(f198,plain,
    ( ~ spl8_6
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f197,f192,f89])).

fof(f89,plain,
    ( spl8_6
  <=> sP7(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f192,plain,
    ( spl8_19
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f197,plain,
    ( ~ sP7(k1_xboole_0)
    | ~ spl8_19 ),
    inference(resolution,[],[f194,f56])).

% (31595)Refutation not found, incomplete strategy% (31595)------------------------------
% (31595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31595)Termination reason: Refutation not found, incomplete strategy

% (31595)Memory used [KB]: 1663
% (31595)Time elapsed: 0.001 s
% (31595)------------------------------
% (31595)------------------------------
fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f52,f55_D])).

fof(f55,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f55_D])).

fof(f55_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f194,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f195,plain,
    ( ~ spl8_1
    | spl8_19
    | spl8_2
    | ~ spl8_4
    | spl8_5
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f190,f138,f78,f73,f63,f192,f58])).

fof(f58,plain,
    ( spl8_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f63,plain,
    ( spl8_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f73,plain,
    ( spl8_4
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

% (31599)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f78,plain,
    ( spl8_5
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f138,plain,
    ( spl8_12
  <=> r2_waybel_0(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f190,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f143,f140])).

fof(f140,plain,
    ( r2_waybel_0(sK0,sK1,k1_xboole_0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f143,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_waybel_0(X3,X4,X5)
      | v2_struct_0(X4)
      | ~ l1_waybel_0(X4,X3)
      | v2_struct_0(X3)
      | r2_hidden(k2_waybel_0(X3,X4,sK3(X3,X4,X5,sK4(u1_struct_0(X4)))),X5)
      | ~ l1_struct_0(X3) ) ),
    inference(resolution,[],[f41,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f141,plain,
    ( spl8_12
    | spl8_3
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f136,f117,f68,f138])).

fof(f68,plain,
    ( spl8_3
  <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f117,plain,
    ( spl8_9
  <=> ! [X0] :
        ( r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0))
        | r2_waybel_0(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f136,plain,
    ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | r2_waybel_0(sK0,sK1,k1_xboole_0)
    | ~ spl8_9 ),
    inference(superposition,[],[f118,f35])).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f118,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0))
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,
    ( spl8_9
    | spl8_2
    | spl8_5
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f115,f73,f58,f78,f63,f117])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0))
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f54,f75])).

fof(f75,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f36,f48])).

fof(f48,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f98,plain,(
    ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl8_7 ),
    inference(resolution,[],[f94,f47])).

fof(f47,plain,(
    ! [X0] : v1_xboole_0(sK5(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f94,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl8_7
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f95,plain,
    ( spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f85,f93,f89])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sP7(k1_xboole_0) ) ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f81,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f29,f78])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f76,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f33,f58])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:18:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.56  % (31618)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (31610)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.59/0.57  % (31611)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.57  % (31603)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.59/0.58  % (31602)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.59/0.58  % (31619)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.58  % (31611)Refutation found. Thanks to Tanya!
% 1.59/0.58  % SZS status Theorem for theBenchmark
% 1.76/0.59  % (31595)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.76/0.59  % SZS output start Proof for theBenchmark
% 1.76/0.59  fof(f199,plain,(
% 1.76/0.59    $false),
% 1.76/0.59    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f95,f98,f119,f141,f195,f198])).
% 1.76/0.59  fof(f198,plain,(
% 1.76/0.59    ~spl8_6 | ~spl8_19),
% 1.76/0.59    inference(avatar_split_clause,[],[f197,f192,f89])).
% 1.76/0.59  fof(f89,plain,(
% 1.76/0.59    spl8_6 <=> sP7(k1_xboole_0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.76/0.59  fof(f192,plain,(
% 1.76/0.59    spl8_19 <=> r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.76/0.59  fof(f197,plain,(
% 1.76/0.59    ~sP7(k1_xboole_0) | ~spl8_19),
% 1.76/0.59    inference(resolution,[],[f194,f56])).
% 1.76/0.59  % (31595)Refutation not found, incomplete strategy% (31595)------------------------------
% 1.76/0.59  % (31595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.59  % (31595)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.59  
% 1.76/0.59  % (31595)Memory used [KB]: 1663
% 1.76/0.59  % (31595)Time elapsed: 0.001 s
% 1.76/0.59  % (31595)------------------------------
% 1.76/0.59  % (31595)------------------------------
% 1.76/0.59  fof(f56,plain,(
% 1.76/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP7(X1)) )),
% 1.76/0.59    inference(general_splitting,[],[f52,f55_D])).
% 1.76/0.59  fof(f55,plain,(
% 1.76/0.59    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP7(X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f55_D])).
% 1.76/0.59  fof(f55_D,plain,(
% 1.76/0.59    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP7(X1)) )),
% 1.76/0.59    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.76/0.59  fof(f52,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f28])).
% 1.76/0.59  fof(f28,plain,(
% 1.76/0.59    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.76/0.59    inference(ennf_transformation,[],[f8])).
% 1.76/0.59  fof(f8,axiom,(
% 1.76/0.59    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.76/0.59  fof(f194,plain,(
% 1.76/0.59    r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0) | ~spl8_19),
% 1.76/0.59    inference(avatar_component_clause,[],[f192])).
% 1.76/0.59  fof(f195,plain,(
% 1.76/0.59    ~spl8_1 | spl8_19 | spl8_2 | ~spl8_4 | spl8_5 | ~spl8_12),
% 1.76/0.59    inference(avatar_split_clause,[],[f190,f138,f78,f73,f63,f192,f58])).
% 1.76/0.59  fof(f58,plain,(
% 1.76/0.59    spl8_1 <=> l1_struct_0(sK0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.76/0.59  fof(f63,plain,(
% 1.76/0.59    spl8_2 <=> v2_struct_0(sK0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.76/0.59  fof(f73,plain,(
% 1.76/0.59    spl8_4 <=> l1_waybel_0(sK1,sK0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.76/0.59  % (31599)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.76/0.59  fof(f78,plain,(
% 1.76/0.59    spl8_5 <=> v2_struct_0(sK1)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.76/0.59  fof(f138,plain,(
% 1.76/0.59    spl8_12 <=> r2_waybel_0(sK0,sK1,k1_xboole_0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.76/0.59  fof(f190,plain,(
% 1.76/0.59    v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0) | ~l1_struct_0(sK0) | ~spl8_12),
% 1.76/0.59    inference(resolution,[],[f143,f140])).
% 1.76/0.59  fof(f140,plain,(
% 1.76/0.59    r2_waybel_0(sK0,sK1,k1_xboole_0) | ~spl8_12),
% 1.76/0.59    inference(avatar_component_clause,[],[f138])).
% 1.76/0.59  fof(f143,plain,(
% 1.76/0.59    ( ! [X4,X5,X3] : (~r2_waybel_0(X3,X4,X5) | v2_struct_0(X4) | ~l1_waybel_0(X4,X3) | v2_struct_0(X3) | r2_hidden(k2_waybel_0(X3,X4,sK3(X3,X4,X5,sK4(u1_struct_0(X4)))),X5) | ~l1_struct_0(X3)) )),
% 1.76/0.59    inference(resolution,[],[f41,f45])).
% 1.76/0.59  fof(f45,plain,(
% 1.76/0.59    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f3])).
% 1.76/0.59  fof(f3,axiom,(
% 1.76/0.59    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.76/0.59  fof(f41,plain,(
% 1.76/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | ~r2_waybel_0(X0,X1,X2)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f22])).
% 1.76/0.59  fof(f22,plain,(
% 1.76/0.59    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.76/0.59    inference(flattening,[],[f21])).
% 1.76/0.59  fof(f21,plain,(
% 1.76/0.59    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.76/0.59    inference(ennf_transformation,[],[f9])).
% 1.76/0.59  fof(f9,axiom,(
% 1.76/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
% 1.76/0.59  fof(f141,plain,(
% 1.76/0.59    spl8_12 | spl8_3 | ~spl8_9),
% 1.76/0.59    inference(avatar_split_clause,[],[f136,f117,f68,f138])).
% 1.76/0.59  fof(f68,plain,(
% 1.76/0.59    spl8_3 <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.76/0.59  fof(f117,plain,(
% 1.76/0.59    spl8_9 <=> ! [X0] : (r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0)) | r2_waybel_0(sK0,sK1,X0))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.76/0.59  fof(f136,plain,(
% 1.76/0.59    r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | r2_waybel_0(sK0,sK1,k1_xboole_0) | ~spl8_9),
% 1.76/0.59    inference(superposition,[],[f118,f35])).
% 1.76/0.59  fof(f35,plain,(
% 1.76/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.76/0.59    inference(cnf_transformation,[],[f2])).
% 1.76/0.59  fof(f2,axiom,(
% 1.76/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.76/0.59  fof(f118,plain,(
% 1.76/0.59    ( ! [X0] : (r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0)) | r2_waybel_0(sK0,sK1,X0)) ) | ~spl8_9),
% 1.76/0.59    inference(avatar_component_clause,[],[f117])).
% 1.76/0.59  fof(f119,plain,(
% 1.76/0.59    spl8_9 | spl8_2 | spl8_5 | ~spl8_1 | ~spl8_4),
% 1.76/0.59    inference(avatar_split_clause,[],[f115,f73,f58,f78,f63,f117])).
% 1.76/0.59  fof(f115,plain,(
% 1.76/0.59    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0)) | r2_waybel_0(sK0,sK1,X0)) ) | ~spl8_4),
% 1.76/0.59    inference(resolution,[],[f54,f75])).
% 1.76/0.59  fof(f75,plain,(
% 1.76/0.59    l1_waybel_0(sK1,sK0) | ~spl8_4),
% 1.76/0.59    inference(avatar_component_clause,[],[f73])).
% 1.76/0.59  fof(f54,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | v2_struct_0(X0) | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2)) )),
% 1.76/0.59    inference(definition_unfolding,[],[f36,f48])).
% 1.76/0.59  fof(f48,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f5])).
% 1.76/0.59  fof(f5,axiom,(
% 1.76/0.59    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.76/0.59  fof(f36,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f20])).
% 1.76/0.59  fof(f20,plain,(
% 1.76/0.59    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.76/0.59    inference(flattening,[],[f19])).
% 1.76/0.59  fof(f19,plain,(
% 1.76/0.59    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.76/0.59    inference(ennf_transformation,[],[f10])).
% 1.76/0.59  fof(f10,axiom,(
% 1.76/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).
% 1.76/0.59  fof(f98,plain,(
% 1.76/0.59    ~spl8_7),
% 1.76/0.59    inference(avatar_contradiction_clause,[],[f97])).
% 1.76/0.59  fof(f97,plain,(
% 1.76/0.59    $false | ~spl8_7),
% 1.76/0.59    inference(resolution,[],[f94,f47])).
% 1.76/0.59  fof(f47,plain,(
% 1.76/0.59    ( ! [X0] : (v1_xboole_0(sK5(X0))) )),
% 1.76/0.59    inference(cnf_transformation,[],[f4])).
% 1.76/0.59  fof(f4,axiom,(
% 1.76/0.59    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 1.76/0.59  fof(f94,plain,(
% 1.76/0.59    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl8_7),
% 1.76/0.59    inference(avatar_component_clause,[],[f93])).
% 1.76/0.59  fof(f93,plain,(
% 1.76/0.59    spl8_7 <=> ! [X0] : ~v1_xboole_0(X0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.76/0.59  fof(f95,plain,(
% 1.76/0.59    spl8_6 | spl8_7),
% 1.76/0.59    inference(avatar_split_clause,[],[f85,f93,f89])).
% 1.76/0.59  fof(f85,plain,(
% 1.76/0.59    ( ! [X0] : (~v1_xboole_0(X0) | sP7(k1_xboole_0)) )),
% 1.76/0.59    inference(resolution,[],[f55,f34])).
% 1.76/0.59  fof(f34,plain,(
% 1.76/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.76/0.59    inference(cnf_transformation,[],[f6])).
% 1.76/0.59  fof(f6,axiom,(
% 1.76/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.76/0.59  fof(f81,plain,(
% 1.76/0.59    ~spl8_5),
% 1.76/0.59    inference(avatar_split_clause,[],[f29,f78])).
% 1.76/0.59  fof(f29,plain,(
% 1.76/0.59    ~v2_struct_0(sK1)),
% 1.76/0.59    inference(cnf_transformation,[],[f18])).
% 1.76/0.59  fof(f18,plain,(
% 1.76/0.59    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.76/0.59    inference(flattening,[],[f17])).
% 1.76/0.59  fof(f17,plain,(
% 1.76/0.59    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.76/0.59    inference(ennf_transformation,[],[f16])).
% 1.76/0.59  fof(f16,plain,(
% 1.76/0.59    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.76/0.59    inference(pure_predicate_removal,[],[f15])).
% 1.76/0.59  fof(f15,plain,(
% 1.76/0.59    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.76/0.59    inference(pure_predicate_removal,[],[f13])).
% 1.76/0.59  fof(f13,negated_conjecture,(
% 1.76/0.59    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.76/0.59    inference(negated_conjecture,[],[f12])).
% 1.76/0.59  fof(f12,conjecture,(
% 1.76/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 1.76/0.59  fof(f76,plain,(
% 1.76/0.59    spl8_4),
% 1.76/0.59    inference(avatar_split_clause,[],[f30,f73])).
% 1.76/0.59  fof(f30,plain,(
% 1.76/0.59    l1_waybel_0(sK1,sK0)),
% 1.76/0.59    inference(cnf_transformation,[],[f18])).
% 1.76/0.59  fof(f71,plain,(
% 1.76/0.59    ~spl8_3),
% 1.76/0.59    inference(avatar_split_clause,[],[f31,f68])).
% 1.76/0.59  fof(f31,plain,(
% 1.76/0.59    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 1.76/0.59    inference(cnf_transformation,[],[f18])).
% 1.76/0.59  fof(f66,plain,(
% 1.76/0.59    ~spl8_2),
% 1.76/0.59    inference(avatar_split_clause,[],[f32,f63])).
% 1.76/0.59  fof(f32,plain,(
% 1.76/0.59    ~v2_struct_0(sK0)),
% 1.76/0.59    inference(cnf_transformation,[],[f18])).
% 1.76/0.59  fof(f61,plain,(
% 1.76/0.59    spl8_1),
% 1.76/0.59    inference(avatar_split_clause,[],[f33,f58])).
% 1.76/0.59  fof(f33,plain,(
% 1.76/0.59    l1_struct_0(sK0)),
% 1.76/0.59    inference(cnf_transformation,[],[f18])).
% 1.76/0.59  % SZS output end Proof for theBenchmark
% 1.76/0.59  % (31611)------------------------------
% 1.76/0.59  % (31611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.59  % (31611)Termination reason: Refutation
% 1.76/0.59  
% 1.76/0.59  % (31611)Memory used [KB]: 10874
% 1.76/0.59  % (31611)Time elapsed: 0.161 s
% 1.76/0.59  % (31611)------------------------------
% 1.76/0.59  % (31611)------------------------------
% 1.76/0.60  % (31599)Refutation not found, incomplete strategy% (31599)------------------------------
% 1.76/0.60  % (31599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (31599)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (31599)Memory used [KB]: 6268
% 1.76/0.60  % (31599)Time elapsed: 0.166 s
% 1.76/0.60  % (31599)------------------------------
% 1.76/0.60  % (31599)------------------------------
% 1.76/0.60  % (31594)Success in time 0.237 s
%------------------------------------------------------------------------------
