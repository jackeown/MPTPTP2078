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
% DateTime   : Thu Dec  3 13:23:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 745 expanded)
%              Number of leaves         :   46 ( 293 expanded)
%              Depth                    :   13
%              Number of atoms          : 1048 (5538 expanded)
%              Number of equality atoms :   19 ( 104 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f271,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f105,f123,f125,f127,f133,f135,f161,f163,f165,f167,f171,f182,f188,f194,f200,f210,f212,f222,f229,f231,f235,f241,f247,f253,f261,f267,f269,f270])).

fof(f270,plain,
    ( spl5_2
    | ~ spl5_1
    | ~ spl5_23
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f257,f250,f239,f97,f101])).

fof(f101,plain,
    ( spl5_2
  <=> r2_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f97,plain,
    ( spl5_1
  <=> r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f239,plain,
    ( spl5_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f250,plain,
    ( spl5_25
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f257,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ spl5_23
    | ~ spl5_25 ),
    inference(resolution,[],[f254,f95])).

% (21858)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% (21854)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% (21870)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% (21869)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% (21868)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% (21864)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% (21862)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (21867)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f95,plain,(
    m1_subset_1(sK2,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f59,f94])).

fof(f94,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f66,f92])).

fof(f92,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f65,f53])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ r2_waybel_7(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    & ( r2_waybel_7(sK0,sK1,sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_waybel_7(X0,X1,X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
                & ( r2_waybel_7(X0,X1,X2)
                  | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(sK0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
              & ( r2_waybel_7(sK0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_waybel_7(sK0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
            & ( r2_waybel_7(sK0,X1,X2)
              | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ( ~ r2_waybel_7(sK0,sK1,X2)
            | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
          & ( r2_waybel_7(sK0,sK1,X2)
            | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ( ~ r2_waybel_7(sK0,sK1,X2)
          | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
        & ( r2_waybel_7(sK0,sK1,X2)
          | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_waybel_7(sK0,sK1,sK2)
        | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
      & ( r2_waybel_7(sK0,sK1,sK2)
        | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
                <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow19)).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f59,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | r2_waybel_7(sK0,sK1,X0) )
    | ~ spl5_23
    | ~ spl5_25 ),
    inference(backward_demodulation,[],[f240,f252])).

fof(f252,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f250])).

fof(f240,plain,
    ( ! [X0] :
        ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f239])).

fof(f269,plain,(
    spl5_27 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | spl5_27 ),
    inference(resolution,[],[f266,f95])).

fof(f266,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl5_27
  <=> m1_subset_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f267,plain,
    ( ~ spl5_27
    | spl5_1
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f262,f259,f101,f97,f264])).

fof(f259,plain,
    ( spl5_26
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ r2_waybel_7(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f262,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(resolution,[],[f260,f103])).

fof(f103,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,sK1,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( ~ spl5_15
    | ~ spl5_5
    | ~ spl5_4
    | spl5_3
    | spl5_26
    | ~ spl5_20
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f256,f250,f220,f259,f108,f112,f116,f191])).

fof(f191,plain,
    ( spl5_15
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f116,plain,
    ( spl5_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f112,plain,
    ( spl5_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f108,plain,
    ( spl5_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f220,plain,
    ( spl5_20
  <=> ! [X1,X0] :
        ( ~ r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK1,X0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) )
    | ~ spl5_20
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f255,f94])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,sK1,X0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_20
    | ~ spl5_25 ),
    inference(superposition,[],[f221,f252])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f220])).

fof(f253,plain,
    ( ~ spl5_17
    | ~ spl5_10
    | ~ spl5_8
    | spl5_11
    | spl5_25
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f248,f245,f250,f150,f138,f146,f203])).

fof(f203,plain,
    ( spl5_17
  <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f146,plain,
    ( spl5_10
  <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f138,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f150,plain,
    ( spl5_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f245,plain,
    ( spl5_24
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
        | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0
        | v1_xboole_0(X0)
        | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f248,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ spl5_24 ),
    inference(resolution,[],[f246,f84])).

fof(f84,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f64,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f55,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
        | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f245])).

fof(f247,plain,
    ( spl5_3
    | spl5_24 ),
    inference(avatar_split_clause,[],[f243,f245,f108])).

fof(f243,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(X0)
      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f85,f92])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f71,f64,f64,f64,f64])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f241,plain,
    ( ~ spl5_5
    | ~ spl5_4
    | spl5_3
    | spl5_23
    | ~ spl5_15
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f237,f233,f191,f239,f108,f112,f116])).

fof(f233,plain,
    ( spl5_22
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    | ~ spl5_15
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f236,f94])).

fof(f236,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_15
    | ~ spl5_22 ),
    inference(resolution,[],[f234,f193])).

fof(f193,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f234,plain,
    ( ! [X2,X3] :
        ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2)
        | ~ r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X3)) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f233])).

% (21857)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f235,plain,
    ( spl5_19
    | ~ spl5_13
    | spl5_22
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f214,f207,f233,f158,f216])).

fof(f216,plain,
    ( spl5_19
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f158,plain,
    ( spl5_13
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f207,plain,
    ( spl5_18
  <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f214,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)
        | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2)
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_18 ),
    inference(resolution,[],[f209,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
                  | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow19)).

fof(f209,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f207])).

fof(f231,plain,(
    spl5_21 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | spl5_21 ),
    inference(resolution,[],[f228,f92])).

fof(f228,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl5_21
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f229,plain,
    ( spl5_3
    | ~ spl5_21
    | spl5_12
    | spl5_11
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f224,f216,f142,f138,f203,f146,f150,f154,f226,f108])).

fof(f154,plain,
    ( spl5_12
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f142,plain,
    ( spl5_9
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f224,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f223,f94])).

fof(f223,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_19 ),
    inference(resolution,[],[f218,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f74,f64,f64,f64])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f218,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f216])).

fof(f222,plain,
    ( spl5_19
    | ~ spl5_13
    | spl5_20
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f213,f207,f220,f158,f216])).

% (21865)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f213,plain,
    ( ! [X0,X1] :
        ( ~ r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_18 ),
    inference(resolution,[],[f209,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f212,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl5_17 ),
    inference(resolution,[],[f205,f82])).

fof(f82,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f57,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f205,plain,
    ( ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f203])).

fof(f210,plain,
    ( ~ spl5_8
    | ~ spl5_17
    | ~ spl5_10
    | ~ spl5_9
    | spl5_11
    | spl5_12
    | spl5_18
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f201,f198,f207,f154,f150,f142,f146,f203,f138])).

fof(f198,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | v7_waybel_0(k3_yellow19(sK0,X1,X0))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f201,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ spl5_16 ),
    inference(resolution,[],[f199,f84])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
        | v7_waybel_0(k3_yellow19(sK0,X1,X0))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f198])).

fof(f200,plain,
    ( spl5_3
    | spl5_16 ),
    inference(avatar_split_clause,[],[f196,f198,f108])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v7_waybel_0(k3_yellow19(sK0,X1,X0))
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f195,f94])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | v7_waybel_0(k3_yellow19(sK0,X1,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f90,f92])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v7_waybel_0(k3_yellow19(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f79,f64,f64,f64,f64])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f194,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | spl5_12
    | spl5_15
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f189,f186,f191,f154,f150,f146,f142,f138])).

fof(f186,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0)
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f189,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ spl5_14 ),
    inference(resolution,[],[f187,f82])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0)
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f186])).

fof(f188,plain,
    ( spl5_3
    | spl5_14 ),
    inference(avatar_split_clause,[],[f184,f186,f108])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f183,f94])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f88,f92])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f77,f64,f64,f64])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f182,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f178,f154,f120,f116,f112,f108])).

fof(f120,plain,
    ( spl5_6
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f178,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(resolution,[],[f177,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f177,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(resolution,[],[f175,f122])).

fof(f122,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | ~ spl5_12 ),
    inference(resolution,[],[f172,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl5_12 ),
    inference(resolution,[],[f156,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f156,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f171,plain,(
    ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl5_11 ),
    inference(resolution,[],[f152,f54])).

fof(f54,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f152,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f167,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl5_10 ),
    inference(resolution,[],[f148,f83])).

fof(f83,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f56,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f148,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f165,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl5_9 ),
    inference(resolution,[],[f144,f93])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f63,f62])).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f144,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f163,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f140,f81])).

fof(f81,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f58,f64])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f43])).

fof(f140,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f161,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | spl5_12
    | spl5_13
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f136,f131,f158,f154,f150,f146,f142,f138])).

fof(f131,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_orders_2(k3_yellow19(sK0,X1,X0))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f136,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ spl5_7 ),
    inference(resolution,[],[f132,f82])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | v4_orders_2(k3_yellow19(sK0,X1,X0))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f135,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl5_3 ),
    inference(resolution,[],[f110,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f110,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f133,plain,
    ( spl5_3
    | spl5_7 ),
    inference(avatar_split_clause,[],[f129,f131,f108])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v4_orders_2(k3_yellow19(sK0,X1,X0))
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f128,f94])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | v4_orders_2(k3_yellow19(sK0,X1,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f92])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v4_orders_2(k3_yellow19(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f75,f64,f64,f64])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f127,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f118,f53])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f125,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f114,f52])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f114,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f123,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f106,f120,f116,f112,f108])).

fof(f106,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f69,f94])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f105,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f61,f101,f97])).

fof(f61,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f60,f101,f97])).

fof(f60,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:39:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (21855)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (21861)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (21863)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (21853)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (21855)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f104,f105,f123,f125,f127,f133,f135,f161,f163,f165,f167,f171,f182,f188,f194,f200,f210,f212,f222,f229,f231,f235,f241,f247,f253,f261,f267,f269,f270])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    spl5_2 | ~spl5_1 | ~spl5_23 | ~spl5_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f257,f250,f239,f97,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl5_2 <=> r2_waybel_7(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl5_1 <=> r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    spl5_23 <=> ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    spl5_25 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | r2_waybel_7(sK0,sK1,sK2) | (~spl5_23 | ~spl5_25)),
% 0.21/0.48    inference(resolution,[],[f254,f95])).
% 0.21/0.48  % (21858)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (21854)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (21870)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (21869)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (21868)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (21864)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (21862)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (21867)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.21/0.49    inference(backward_demodulation,[],[f59,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f66,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    l1_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f65,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    (((~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42,f41,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_waybel_7(sK0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & (r2_waybel_7(sK0,X1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : ((~r2_waybel_7(sK0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & (r2_waybel_7(sK0,X1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r2_waybel_7(sK0,sK1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ? [X2] : ((~r2_waybel_7(sK0,sK1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f14])).
% 0.21/0.49  fof(f14,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow19)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | r2_waybel_7(sK0,sK1,X0)) ) | (~spl5_23 | ~spl5_25)),
% 0.21/0.49    inference(backward_demodulation,[],[f240,f252])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl5_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f250])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ( ! [X0] : (r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | ~spl5_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f239])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    spl5_27),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f268])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    $false | spl5_27),
% 0.21/0.49    inference(resolution,[],[f266,f95])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k2_struct_0(sK0)) | spl5_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f264])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    spl5_27 <=> m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ~spl5_27 | spl5_1 | ~spl5_2 | ~spl5_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f262,f259,f101,f97,f264])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    spl5_26 <=> ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~r2_waybel_7(sK0,sK1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl5_2 | ~spl5_26)),
% 0.21/0.49    inference(resolution,[],[f260,f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    r2_waybel_7(sK0,sK1,sK2) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_waybel_7(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | ~spl5_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f259])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    ~spl5_15 | ~spl5_5 | ~spl5_4 | spl5_3 | spl5_26 | ~spl5_20 | ~spl5_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f256,f250,f220,f259,f108,f112,f116,f191])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl5_15 <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl5_5 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl5_4 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl5_3 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    spl5_20 <=> ! [X1,X0] : (~r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_waybel_7(sK0,sK1,X0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)) ) | (~spl5_20 | ~spl5_25)),
% 0.21/0.49    inference(forward_demodulation,[],[f255,f94])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_waybel_7(sK0,sK1,X0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl5_20 | ~spl5_25)),
% 0.21/0.49    inference(superposition,[],[f221,f252])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) ) | ~spl5_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f220])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    ~spl5_17 | ~spl5_10 | ~spl5_8 | spl5_11 | spl5_25 | ~spl5_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f248,f245,f250,f150,f138,f146,f203])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    spl5_17 <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl5_10 <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    spl5_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl5_11 <=> v1_xboole_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    spl5_24 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 | v1_xboole_0(X0) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~spl5_24),
% 0.21/0.49    inference(resolution,[],[f246,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.21/0.49    inference(definition_unfolding,[],[f55,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ) | ~spl5_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f245])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    spl5_3 | spl5_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f243,f245,f108])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(X0) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f85,f92])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | v2_struct_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f71,f64,f64,f64,f64])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ~spl5_5 | ~spl5_4 | spl5_3 | spl5_23 | ~spl5_15 | ~spl5_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f237,f233,f191,f239,f108,f112,f116])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    spl5_22 <=> ! [X3,X2] : (~r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) | ~m1_subset_1(X2,u1_struct_0(X3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) ) | (~spl5_15 | ~spl5_22)),
% 0.21/0.49    inference(forward_demodulation,[],[f236,f94])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl5_15 | ~spl5_22)),
% 0.21/0.49    inference(resolution,[],[f234,f193])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~spl5_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f191])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2) | ~r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X2,u1_struct_0(X3))) ) | ~spl5_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f233])).
% 0.21/0.49  % (21857)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    spl5_19 | ~spl5_13 | spl5_22 | ~spl5_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f214,f207,f233,f158,f216])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    spl5_19 <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    spl5_13 <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    spl5_18 <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r2_hidden(X2,k10_yellow_6(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X2,u1_struct_0(X3)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) | r2_waybel_7(X3,k2_yellow19(X3,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X2) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_18),
% 0.21/0.49    inference(resolution,[],[f209,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow19)).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl5_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f207])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    spl5_21),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f230])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    $false | spl5_21),
% 0.21/0.49    inference(resolution,[],[f228,f92])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | spl5_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f226])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    spl5_21 <=> l1_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    spl5_3 | ~spl5_21 | spl5_12 | spl5_11 | ~spl5_10 | ~spl5_17 | ~spl5_8 | ~spl5_9 | ~spl5_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f224,f216,f142,f138,f203,f146,f150,f154,f226,f108])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl5_12 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl5_9 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_19),
% 0.21/0.49    inference(forward_demodulation,[],[f223,f94])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_19),
% 0.21/0.49    inference(resolution,[],[f218,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f74,f64,f64,f64])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl5_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f216])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    spl5_19 | ~spl5_13 | spl5_20 | ~spl5_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f213,f207,f220,f158,f216])).
% 0.21/0.49  % (21865)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r2_hidden(X1,k10_yellow_6(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl5_18),
% 0.21/0.49    inference(resolution,[],[f209,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    spl5_17),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    $false | spl5_17),
% 0.21/0.49    inference(resolution,[],[f205,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.49    inference(definition_unfolding,[],[f57,f64])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | spl5_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f203])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ~spl5_8 | ~spl5_17 | ~spl5_10 | ~spl5_9 | spl5_11 | spl5_12 | spl5_18 | ~spl5_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f201,f198,f207,f154,f150,f142,f146,f203,f138])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    spl5_16 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v7_waybel_0(k3_yellow19(sK0,X1,X0)) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~spl5_16),
% 0.21/0.49    inference(resolution,[],[f199,f84])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v7_waybel_0(k3_yellow19(sK0,X1,X0)) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))) ) | ~spl5_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f198])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    spl5_3 | spl5_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f196,f198,f108])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X0) | v1_xboole_0(X1) | v7_waybel_0(k3_yellow19(sK0,X1,X0)) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f195,f94])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | v7_waybel_0(k3_yellow19(sK0,X1,X0)) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f90,f92])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | v7_waybel_0(k3_yellow19(X0,X1,X2)) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f79,f64,f64,f64,f64])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_11 | spl5_12 | spl5_15 | ~spl5_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f189,f186,f191,f154,f150,f146,f142,f138])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    spl5_14 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~spl5_14),
% 0.21/0.49    inference(resolution,[],[f187,f82])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))) ) | ~spl5_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f186])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    spl5_3 | spl5_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f184,f186,f108])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X0) | v1_xboole_0(X1) | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f183,f94])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | l1_waybel_0(k3_yellow19(sK0,X1,X0),sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f88,f92])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f77,f64,f64,f64])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f178,f154,f120,f116,f112,f108])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl5_6 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_12)),
% 0.21/0.49    inference(resolution,[],[f177,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0] : ((~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    v1_xboole_0(sK3(sK0)) | (~spl5_6 | ~spl5_12)),
% 0.21/0.49    inference(resolution,[],[f175,f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(X0)) ) | ~spl5_12),
% 0.21/0.49    inference(resolution,[],[f172,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(rectify,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl5_12),
% 0.21/0.49    inference(resolution,[],[f156,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | ~spl5_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f154])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ~spl5_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    $false | ~spl5_11),
% 0.21/0.49    inference(resolution,[],[f152,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~spl5_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f150])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    spl5_10),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    $false | spl5_10),
% 0.21/0.49    inference(resolution,[],[f148,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.49    inference(definition_unfolding,[],[f56,f64])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | spl5_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f146])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    spl5_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    $false | spl5_9),
% 0.21/0.49    inference(resolution,[],[f144,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f63,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl5_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f142])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl5_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    $false | spl5_8),
% 0.21/0.49    inference(resolution,[],[f140,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.21/0.49    inference(definition_unfolding,[],[f58,f64])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | spl5_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f138])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_11 | spl5_12 | spl5_13 | ~spl5_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f136,f131,f158,f154,f150,f146,f142,f138])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl5_7 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v4_orders_2(k3_yellow19(sK0,X1,X0)) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~spl5_7),
% 0.21/0.49    inference(resolution,[],[f132,f82])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | v4_orders_2(k3_yellow19(sK0,X1,X0)) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))) ) | ~spl5_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f131])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ~spl5_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f134])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    $false | ~spl5_3),
% 0.21/0.49    inference(resolution,[],[f110,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl5_3 | spl5_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f129,f131,f108])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X0) | v1_xboole_0(X1) | v4_orders_2(k3_yellow19(sK0,X1,X0)) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f128,f94])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | v4_orders_2(k3_yellow19(sK0,X1,X0)) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f86,f92])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | v4_orders_2(k3_yellow19(X0,X1,X2)) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f75,f64,f64,f64])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl5_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    $false | spl5_5),
% 0.21/0.49    inference(resolution,[],[f118,f53])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f116])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl5_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    $false | spl5_4),
% 0.21/0.49    inference(resolution,[],[f114,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | spl5_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f106,f120,f116,f112,f108])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(superposition,[],[f69,f94])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ~spl5_1 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f61,f101,f97])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl5_1 | spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f101,f97])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (21855)------------------------------
% 0.21/0.49  % (21855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21855)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (21855)Memory used [KB]: 6268
% 0.21/0.49  % (21855)Time elapsed: 0.059 s
% 0.21/0.49  % (21855)------------------------------
% 0.21/0.49  % (21855)------------------------------
% 0.21/0.49  % (21852)Success in time 0.129 s
%------------------------------------------------------------------------------
