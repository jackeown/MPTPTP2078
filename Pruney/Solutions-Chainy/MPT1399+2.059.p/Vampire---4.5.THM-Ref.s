%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:20 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 192 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  297 ( 777 expanded)
%              Number of equality atoms :   21 (  67 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f505,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f179,f187,f189,f191,f193,f218,f421,f422,f424,f500,f501,f504])).

fof(f504,plain,(
    ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | ~ spl5_26 ),
    inference(resolution,[],[f247,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

% (25811)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% (25826)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (25823)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% (25827)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% (25812)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (25812)Refutation not found, incomplete strategy% (25812)------------------------------
% (25812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25812)Termination reason: Refutation not found, incomplete strategy

% (25812)Memory used [KB]: 6140
% (25812)Time elapsed: 0.112 s
% (25812)------------------------------
% (25812)------------------------------
% (25816)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (25828)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% (25820)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% (25822)Refutation not found, incomplete strategy% (25822)------------------------------
% (25822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25822)Termination reason: Refutation not found, incomplete strategy

% (25822)Memory used [KB]: 1663
% (25822)Time elapsed: 0.072 s
% (25822)------------------------------
% (25822)------------------------------
% (25828)Refutation not found, incomplete strategy% (25828)------------------------------
% (25828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25828)Termination reason: Refutation not found, incomplete strategy

% (25828)Memory used [KB]: 10618
% (25828)Time elapsed: 0.120 s
% (25828)------------------------------
% (25828)------------------------------
% (25808)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% (25809)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% (25805)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% (25808)Refutation not found, incomplete strategy% (25808)------------------------------
% (25808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25808)Termination reason: Refutation not found, incomplete strategy

% (25808)Memory used [KB]: 10618
% (25808)Time elapsed: 0.131 s
% (25808)------------------------------
% (25808)------------------------------
% (25824)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% (25826)Refutation not found, incomplete strategy% (25826)------------------------------
% (25826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25826)Termination reason: Refutation not found, incomplete strategy

% (25826)Memory used [KB]: 1791
% (25826)Time elapsed: 0.129 s
% (25826)------------------------------
% (25826)------------------------------
fof(f247,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl5_26
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f501,plain,
    ( spl5_26
    | ~ spl5_21
    | ~ spl5_20
    | ~ spl5_27
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f441,f159,f249,f182,f185,f246])).

fof(f185,plain,
    ( spl5_21
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f182,plain,
    ( spl5_20
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f249,plain,
    ( spl5_27
  <=> v2_tops_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f159,plain,
    ( spl5_16
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f441,plain,
    ( ~ v2_tops_1(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_16 ),
    inference(superposition,[],[f53,f427])).

fof(f427,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f160,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f160,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_tops_1(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).

fof(f500,plain,
    ( ~ spl5_21
    | spl5_27
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f496,f177,f249,f185])).

fof(f177,plain,
    ( spl5_19
  <=> ! [X5] : ~ r2_hidden(X5,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f496,plain,
    ( v2_tops_1(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_19 ),
    inference(superposition,[],[f52,f478])).

fof(f478,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ spl5_19 ),
    inference(resolution,[],[f178,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f178,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK3(sK0))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f52,plain,(
    ! [X0] :
      ( v2_tops_1(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).

fof(f424,plain,
    ( ~ spl5_15
    | spl5_16
    | spl5_11 ),
    inference(avatar_split_clause,[],[f423,f137,f159,f156])).

fof(f156,plain,
    ( spl5_15
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f137,plain,
    ( spl5_11
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f423,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl5_11 ),
    inference(resolution,[],[f138,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f138,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f422,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f413,f146,f143,f140,f137])).

fof(f140,plain,
    ( spl5_12
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f143,plain,
    ( spl5_13
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f146,plain,
    ( spl5_14
  <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f413,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f133,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f47,f46])).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f133,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X3,k1_xboole_0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(forward_demodulation,[],[f132,f40])).

fof(f40,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f132,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2) ) ),
    inference(forward_demodulation,[],[f38,f81])).

fof(f81,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f79,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f48,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f38,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f421,plain,(
    ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | ~ spl5_14 ),
    inference(resolution,[],[f403,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f403,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_struct_0(sK0))
    | ~ spl5_14 ),
    inference(resolution,[],[f147,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f147,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f218,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl5_15 ),
    inference(resolution,[],[f157,f108])).

fof(f108,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f41,f81])).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f157,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f193,plain,(
    spl5_21 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl5_21 ),
    inference(resolution,[],[f186,f44])).

fof(f186,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f185])).

fof(f191,plain,(
    spl5_20 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl5_20 ),
    inference(resolution,[],[f183,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f183,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f189,plain,
    ( ~ spl5_20
    | ~ spl5_21
    | spl5_13 ),
    inference(avatar_split_clause,[],[f188,f143,f185,f182])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_13 ),
    inference(resolution,[],[f144,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f144,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f187,plain,
    ( ~ spl5_20
    | ~ spl5_21
    | spl5_12 ),
    inference(avatar_split_clause,[],[f180,f140,f185,f182])).

fof(f180,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_12 ),
    inference(resolution,[],[f141,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f141,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f179,plain,
    ( ~ spl5_16
    | spl5_19 ),
    inference(avatar_split_clause,[],[f165,f177,f159])).

fof(f165,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK3(sK0))
      | ~ v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f59,f110])).

fof(f110,plain,(
    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(global_subsumption,[],[f44,f109])).

fof(f109,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f51,f81])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:56:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (25821)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.50  % (25813)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.50  % (25813)Refutation not found, incomplete strategy% (25813)------------------------------
% 0.22/0.50  % (25813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25821)Refutation not found, incomplete strategy% (25821)------------------------------
% 0.22/0.50  % (25821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25821)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25821)Memory used [KB]: 1663
% 0.22/0.50  % (25821)Time elapsed: 0.072 s
% 0.22/0.50  % (25821)------------------------------
% 0.22/0.50  % (25821)------------------------------
% 0.22/0.51  % (25813)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25813)Memory used [KB]: 10618
% 0.22/0.51  % (25813)Time elapsed: 0.066 s
% 0.22/0.51  % (25813)------------------------------
% 0.22/0.51  % (25813)------------------------------
% 0.22/0.51  % (25814)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (25807)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (25825)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (25825)Refutation not found, incomplete strategy% (25825)------------------------------
% 0.22/0.52  % (25825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25825)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25825)Memory used [KB]: 6140
% 0.22/0.52  % (25825)Time elapsed: 0.102 s
% 0.22/0.52  % (25825)------------------------------
% 0.22/0.52  % (25825)------------------------------
% 0.22/0.52  % (25806)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.53  % (25818)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.53  % (25817)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.27/0.53  % (25819)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.27/0.53  % (25815)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.27/0.53  % (25822)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.27/0.53  % (25815)Refutation not found, incomplete strategy% (25815)------------------------------
% 1.27/0.53  % (25815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (25815)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (25815)Memory used [KB]: 10618
% 1.27/0.53  % (25815)Time elapsed: 0.108 s
% 1.27/0.53  % (25815)------------------------------
% 1.27/0.53  % (25815)------------------------------
% 1.27/0.53  % (25810)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.27/0.53  % (25817)Refutation found. Thanks to Tanya!
% 1.27/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.53  % SZS output start Proof for theBenchmark
% 1.27/0.53  fof(f505,plain,(
% 1.27/0.53    $false),
% 1.27/0.53    inference(avatar_sat_refutation,[],[f179,f187,f189,f191,f193,f218,f421,f422,f424,f500,f501,f504])).
% 1.27/0.53  fof(f504,plain,(
% 1.27/0.53    ~spl5_26),
% 1.27/0.53    inference(avatar_contradiction_clause,[],[f503])).
% 1.27/0.53  fof(f503,plain,(
% 1.27/0.53    $false | ~spl5_26),
% 1.27/0.53    inference(resolution,[],[f247,f42])).
% 1.27/0.53  fof(f42,plain,(
% 1.27/0.53    ~v2_struct_0(sK0)),
% 1.27/0.53    inference(cnf_transformation,[],[f19])).
% 1.27/0.53  fof(f19,plain,(
% 1.27/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.27/0.53    inference(flattening,[],[f18])).
% 1.27/0.53  fof(f18,plain,(
% 1.27/0.53    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.27/0.53    inference(ennf_transformation,[],[f16])).
% 1.27/0.53  fof(f16,negated_conjecture,(
% 1.27/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.27/0.53    inference(negated_conjecture,[],[f15])).
% 1.27/0.53  fof(f15,conjecture,(
% 1.27/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 1.27/0.53  % (25811)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.27/0.54  % (25826)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.27/0.54  % (25823)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.27/0.54  % (25827)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.27/0.54  % (25812)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.27/0.54  % (25812)Refutation not found, incomplete strategy% (25812)------------------------------
% 1.27/0.54  % (25812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (25812)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (25812)Memory used [KB]: 6140
% 1.27/0.54  % (25812)Time elapsed: 0.112 s
% 1.27/0.54  % (25812)------------------------------
% 1.27/0.54  % (25812)------------------------------
% 1.27/0.54  % (25816)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.27/0.54  % (25828)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.27/0.54  % (25820)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.27/0.54  % (25822)Refutation not found, incomplete strategy% (25822)------------------------------
% 1.27/0.54  % (25822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (25822)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (25822)Memory used [KB]: 1663
% 1.27/0.54  % (25822)Time elapsed: 0.072 s
% 1.27/0.54  % (25822)------------------------------
% 1.27/0.54  % (25822)------------------------------
% 1.27/0.54  % (25828)Refutation not found, incomplete strategy% (25828)------------------------------
% 1.27/0.54  % (25828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (25828)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (25828)Memory used [KB]: 10618
% 1.27/0.54  % (25828)Time elapsed: 0.120 s
% 1.27/0.54  % (25828)------------------------------
% 1.27/0.54  % (25828)------------------------------
% 1.27/0.54  % (25808)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.27/0.54  % (25809)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.44/0.55  % (25805)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.44/0.55  % (25808)Refutation not found, incomplete strategy% (25808)------------------------------
% 1.44/0.55  % (25808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (25808)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (25808)Memory used [KB]: 10618
% 1.44/0.55  % (25808)Time elapsed: 0.131 s
% 1.44/0.55  % (25808)------------------------------
% 1.44/0.55  % (25808)------------------------------
% 1.44/0.55  % (25824)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.44/0.55  % (25826)Refutation not found, incomplete strategy% (25826)------------------------------
% 1.44/0.55  % (25826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (25826)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (25826)Memory used [KB]: 1791
% 1.44/0.55  % (25826)Time elapsed: 0.129 s
% 1.44/0.55  % (25826)------------------------------
% 1.44/0.55  % (25826)------------------------------
% 1.44/0.56  fof(f247,plain,(
% 1.44/0.56    v2_struct_0(sK0) | ~spl5_26),
% 1.44/0.56    inference(avatar_component_clause,[],[f246])).
% 1.44/0.56  fof(f246,plain,(
% 1.44/0.56    spl5_26 <=> v2_struct_0(sK0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.44/0.56  fof(f501,plain,(
% 1.44/0.56    spl5_26 | ~spl5_21 | ~spl5_20 | ~spl5_27 | ~spl5_16),
% 1.44/0.56    inference(avatar_split_clause,[],[f441,f159,f249,f182,f185,f246])).
% 1.44/0.56  fof(f185,plain,(
% 1.44/0.56    spl5_21 <=> l1_pre_topc(sK0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.44/0.56  fof(f182,plain,(
% 1.44/0.56    spl5_20 <=> v2_pre_topc(sK0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.44/0.56  fof(f249,plain,(
% 1.44/0.56    spl5_27 <=> v2_tops_1(k1_xboole_0,sK0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.44/0.56  fof(f159,plain,(
% 1.44/0.56    spl5_16 <=> v1_xboole_0(k2_struct_0(sK0))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.44/0.56  fof(f441,plain,(
% 1.44/0.56    ~v2_tops_1(k1_xboole_0,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_16),
% 1.44/0.56    inference(superposition,[],[f53,f427])).
% 1.44/0.56  fof(f427,plain,(
% 1.44/0.56    k1_xboole_0 = k2_struct_0(sK0) | ~spl5_16),
% 1.44/0.56    inference(resolution,[],[f160,f49])).
% 1.44/0.56  fof(f49,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f21])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.44/0.56  fof(f160,plain,(
% 1.44/0.56    v1_xboole_0(k2_struct_0(sK0)) | ~spl5_16),
% 1.44/0.56    inference(avatar_component_clause,[],[f159])).
% 1.44/0.56  fof(f53,plain,(
% 1.44/0.56    ( ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.56    inference(flattening,[],[f24])).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f14])).
% 1.44/0.56  fof(f14,axiom,(
% 1.44/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ~v2_tops_1(k2_struct_0(X0),X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).
% 1.44/0.56  fof(f500,plain,(
% 1.44/0.56    ~spl5_21 | spl5_27 | ~spl5_19),
% 1.44/0.56    inference(avatar_split_clause,[],[f496,f177,f249,f185])).
% 1.44/0.56  fof(f177,plain,(
% 1.44/0.56    spl5_19 <=> ! [X5] : ~r2_hidden(X5,sK3(sK0))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.44/0.56  fof(f496,plain,(
% 1.44/0.56    v2_tops_1(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | ~spl5_19),
% 1.44/0.56    inference(superposition,[],[f52,f478])).
% 1.44/0.56  fof(f478,plain,(
% 1.44/0.56    k1_xboole_0 = sK3(sK0) | ~spl5_19),
% 1.44/0.56    inference(resolution,[],[f178,f56])).
% 1.44/0.56  fof(f56,plain,(
% 1.44/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.44/0.56    inference(ennf_transformation,[],[f17])).
% 1.44/0.56  fof(f17,plain,(
% 1.44/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.44/0.56    inference(pure_predicate_removal,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 1.44/0.56  fof(f178,plain,(
% 1.44/0.56    ( ! [X5] : (~r2_hidden(X5,sK3(sK0))) ) | ~spl5_19),
% 1.44/0.56    inference(avatar_component_clause,[],[f177])).
% 1.44/0.56  fof(f52,plain,(
% 1.44/0.56    ( ! [X0] : (v2_tops_1(sK3(X0),X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    ! [X0] : (? [X1] : (v2_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,axiom,(
% 1.44/0.56    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v2_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).
% 1.44/0.56  fof(f424,plain,(
% 1.44/0.56    ~spl5_15 | spl5_16 | spl5_11),
% 1.44/0.56    inference(avatar_split_clause,[],[f423,f137,f159,f156])).
% 1.44/0.56  fof(f156,plain,(
% 1.44/0.56    spl5_15 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.44/0.56  fof(f137,plain,(
% 1.44/0.56    spl5_11 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.44/0.56  fof(f423,plain,(
% 1.44/0.56    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k2_struct_0(sK0)) | spl5_11),
% 1.44/0.56    inference(resolution,[],[f138,f57])).
% 1.44/0.56  fof(f57,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.44/0.56    inference(flattening,[],[f31])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.44/0.56  fof(f138,plain,(
% 1.44/0.56    ~r2_hidden(sK1,k2_struct_0(sK0)) | spl5_11),
% 1.44/0.56    inference(avatar_component_clause,[],[f137])).
% 1.44/0.56  fof(f422,plain,(
% 1.44/0.56    ~spl5_11 | ~spl5_12 | ~spl5_13 | spl5_14),
% 1.44/0.56    inference(avatar_split_clause,[],[f413,f146,f143,f140,f137])).
% 1.44/0.56  fof(f140,plain,(
% 1.44/0.56    spl5_12 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.44/0.56  fof(f143,plain,(
% 1.44/0.56    spl5_13 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.44/0.56  fof(f146,plain,(
% 1.44/0.56    spl5_14 <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.44/0.56  fof(f413,plain,(
% 1.44/0.56    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0))),
% 1.44/0.56    inference(resolution,[],[f133,f61])).
% 1.44/0.56  fof(f61,plain,(
% 1.44/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.44/0.56    inference(forward_demodulation,[],[f47,f46])).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.44/0.56  fof(f47,plain,(
% 1.44/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f4])).
% 1.44/0.56  fof(f4,axiom,(
% 1.44/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.44/0.56  fof(f133,plain,(
% 1.44/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 1.44/0.56    inference(forward_demodulation,[],[f132,f40])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    k1_xboole_0 = sK2),
% 1.44/0.56    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f132,plain,(
% 1.44/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | r2_hidden(X3,sK2)) )),
% 1.44/0.56    inference(forward_demodulation,[],[f38,f81])).
% 1.44/0.56  fof(f81,plain,(
% 1.44/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.44/0.56    inference(resolution,[],[f79,f44])).
% 1.44/0.56  fof(f44,plain,(
% 1.44/0.56    l1_pre_topc(sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f79,plain,(
% 1.44/0.56    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.44/0.56    inference(resolution,[],[f48,f50])).
% 1.44/0.56  fof(f50,plain,(
% 1.44/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f22])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,axiom,(
% 1.44/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.44/0.56  fof(f48,plain,(
% 1.44/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f9])).
% 1.44/0.56  fof(f9,axiom,(
% 1.44/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | r2_hidden(X3,sK2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f421,plain,(
% 1.44/0.56    ~spl5_14),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f420])).
% 1.44/0.56  fof(f420,plain,(
% 1.44/0.56    $false | ~spl5_14),
% 1.44/0.56    inference(resolution,[],[f403,f45])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.44/0.56  fof(f403,plain,(
% 1.44/0.56    ~r1_tarski(k1_xboole_0,k2_struct_0(sK0)) | ~spl5_14),
% 1.44/0.56    inference(resolution,[],[f147,f58])).
% 1.44/0.56  fof(f58,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f33])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f7])).
% 1.44/0.56  fof(f7,axiom,(
% 1.44/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.44/0.56  fof(f147,plain,(
% 1.44/0.56    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~spl5_14),
% 1.44/0.56    inference(avatar_component_clause,[],[f146])).
% 1.44/0.56  fof(f218,plain,(
% 1.44/0.56    spl5_15),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f217])).
% 1.44/0.56  fof(f217,plain,(
% 1.44/0.56    $false | spl5_15),
% 1.44/0.56    inference(resolution,[],[f157,f108])).
% 1.44/0.56  fof(f108,plain,(
% 1.44/0.56    m1_subset_1(sK1,k2_struct_0(sK0))),
% 1.44/0.56    inference(backward_demodulation,[],[f41,f81])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.44/0.56    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f157,plain,(
% 1.44/0.56    ~m1_subset_1(sK1,k2_struct_0(sK0)) | spl5_15),
% 1.44/0.56    inference(avatar_component_clause,[],[f156])).
% 1.44/0.56  fof(f193,plain,(
% 1.44/0.56    spl5_21),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f192])).
% 1.44/0.56  fof(f192,plain,(
% 1.44/0.56    $false | spl5_21),
% 1.44/0.56    inference(resolution,[],[f186,f44])).
% 1.44/0.56  fof(f186,plain,(
% 1.44/0.56    ~l1_pre_topc(sK0) | spl5_21),
% 1.44/0.56    inference(avatar_component_clause,[],[f185])).
% 1.44/0.56  fof(f191,plain,(
% 1.44/0.56    spl5_20),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f190])).
% 1.44/0.56  fof(f190,plain,(
% 1.44/0.56    $false | spl5_20),
% 1.44/0.56    inference(resolution,[],[f183,f43])).
% 1.44/0.56  fof(f43,plain,(
% 1.44/0.56    v2_pre_topc(sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f183,plain,(
% 1.44/0.56    ~v2_pre_topc(sK0) | spl5_20),
% 1.44/0.56    inference(avatar_component_clause,[],[f182])).
% 1.44/0.56  fof(f189,plain,(
% 1.44/0.56    ~spl5_20 | ~spl5_21 | spl5_13),
% 1.44/0.56    inference(avatar_split_clause,[],[f188,f143,f185,f182])).
% 1.44/0.56  fof(f188,plain,(
% 1.44/0.56    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_13),
% 1.44/0.56    inference(resolution,[],[f144,f54])).
% 1.44/0.56  fof(f54,plain,(
% 1.44/0.56    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f27])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.44/0.56    inference(flattening,[],[f26])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f12])).
% 1.44/0.56  fof(f12,axiom,(
% 1.44/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.44/0.56  fof(f144,plain,(
% 1.44/0.56    ~v3_pre_topc(k2_struct_0(sK0),sK0) | spl5_13),
% 1.44/0.56    inference(avatar_component_clause,[],[f143])).
% 1.44/0.56  fof(f187,plain,(
% 1.44/0.56    ~spl5_20 | ~spl5_21 | spl5_12),
% 1.44/0.56    inference(avatar_split_clause,[],[f180,f140,f185,f182])).
% 1.44/0.56  fof(f180,plain,(
% 1.44/0.56    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_12),
% 1.44/0.56    inference(resolution,[],[f141,f55])).
% 1.44/0.56  fof(f55,plain,(
% 1.44/0.56    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.44/0.56    inference(flattening,[],[f28])).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f11])).
% 1.44/0.56  fof(f11,axiom,(
% 1.44/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 1.44/0.56  fof(f141,plain,(
% 1.44/0.56    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl5_12),
% 1.44/0.56    inference(avatar_component_clause,[],[f140])).
% 1.44/0.56  fof(f179,plain,(
% 1.44/0.56    ~spl5_16 | spl5_19),
% 1.44/0.56    inference(avatar_split_clause,[],[f165,f177,f159])).
% 1.44/0.56  fof(f165,plain,(
% 1.44/0.56    ( ! [X5] : (~r2_hidden(X5,sK3(sK0)) | ~v1_xboole_0(k2_struct_0(sK0))) )),
% 1.44/0.56    inference(resolution,[],[f59,f110])).
% 1.44/0.56  fof(f110,plain,(
% 1.44/0.56    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.44/0.56    inference(global_subsumption,[],[f44,f109])).
% 1.44/0.56  fof(f109,plain,(
% 1.44/0.56    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.44/0.56    inference(superposition,[],[f51,f81])).
% 1.44/0.56  fof(f51,plain,(
% 1.44/0.56    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f59,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f34])).
% 1.44/0.56  fof(f34,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (25817)------------------------------
% 1.44/0.56  % (25817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (25817)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (25817)Memory used [KB]: 10746
% 1.44/0.56  % (25817)Time elapsed: 0.117 s
% 1.44/0.56  % (25817)------------------------------
% 1.44/0.56  % (25817)------------------------------
% 1.44/0.56  % (25804)Success in time 0.19 s
%------------------------------------------------------------------------------
