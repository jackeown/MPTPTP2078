%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:42 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 538 expanded)
%              Number of leaves         :   14 ( 124 expanded)
%              Depth                    :   22
%              Number of atoms          :  696 (4259 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f224,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f56,f61,f66,f71,f76,f114,f167,f173,f183,f202,f217,f223])).

fof(f223,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f50,f221])).

fof(f221,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f220,f27])).

fof(f27,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                <=> ( r2_orders_2(X0,X1,X2)
                  <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

% (16837)Refutation not found, incomplete strategy% (16837)------------------------------
% (16837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16837)Termination reason: Refutation not found, incomplete strategy

% (16837)Memory used [KB]: 6652
% (16837)Time elapsed: 0.063 s
% (16837)------------------------------
% (16837)------------------------------
% (16831)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (16843)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <=> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_orders_2)).

fof(f220,plain,
    ( ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f219,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f219,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f218,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f218,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f203,f28])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f203,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f53,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r2_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

fof(f53,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_3
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f50,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_2
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f217,plain,
    ( ~ spl5_3
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl5_3
    | spl5_11 ),
    inference(subsumption_resolution,[],[f215,f26])).

fof(f26,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f215,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl5_3
    | spl5_11 ),
    inference(subsumption_resolution,[],[f214,f53])).

fof(f214,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | spl5_11 ),
    inference(subsumption_resolution,[],[f213,f24])).

fof(f213,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | spl5_11 ),
    inference(subsumption_resolution,[],[f212,f25])).

fof(f212,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | spl5_11 ),
    inference(subsumption_resolution,[],[f210,f28])).

fof(f210,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | spl5_11 ),
    inference(resolution,[],[f196,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(sK4(X0,X1,X2),X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

fof(f196,plain,
    ( ~ v6_orders_2(sK4(sK0,sK1,sK2),sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl5_11
  <=> v6_orders_2(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f202,plain,
    ( ~ spl5_3
    | ~ spl5_11
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f201,f45,f194,f52])).

fof(f45,plain,
    ( spl5_1
  <=> ! [X3] :
        ( ~ v6_orders_2(X3,sK0)
        | ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f201,plain,
    ( ~ v6_orders_2(sK4(sK0,sK1,sK2),sK0)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f200,f26])).

fof(f200,plain,
    ( ~ v6_orders_2(sK4(sK0,sK1,sK2),sK0)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f199,f24])).

fof(f199,plain,
    ( ~ v6_orders_2(sK4(sK0,sK1,sK2),sK0)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f198,f28])).

fof(f198,plain,
    ( ~ v6_orders_2(sK4(sK0,sK1,sK2),sK0)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f150,f25])).

fof(f150,plain,
    ( ~ v6_orders_2(sK4(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( ~ v6_orders_2(sK4(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v3_orders_2(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f143,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,sK4(sK0,X0,sK2))
        | ~ v6_orders_2(sK4(sK0,X0,sK2),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f142,f26])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,sK4(sK0,X0,sK2))
        | ~ v6_orders_2(sK4(sK0,X0,sK2),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ v3_orders_2(sK0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f141,f28])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,sK4(sK0,X0,sK2))
        | ~ v6_orders_2(sK4(sK0,X0,sK2),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f140,f24])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,sK4(sK0,X0,sK2))
        | ~ v6_orders_2(sK4(sK0,X0,sK2),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,sK4(sK0,X0,sK2))
        | ~ v6_orders_2(sK4(sK0,X0,sK2),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ v3_orders_2(sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f130,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2,sK4(sK0,X0,X1))
        | ~ r2_hidden(sK1,sK4(sK0,X0,X1))
        | ~ v6_orders_2(sK4(sK0,X0,X1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f129,f26])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2,sK4(sK0,X0,X1))
        | ~ r2_hidden(sK1,sK4(sK0,X0,X1))
        | ~ v6_orders_2(sK4(sK0,X0,X1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ v3_orders_2(sK0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f123,f28])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2,sK4(sK0,X0,X1))
        | ~ r2_hidden(sK1,sK4(sK0,X0,X1))
        | ~ v6_orders_2(sK4(sK0,X0,X1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ v3_orders_2(sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(sK1,X3)
        | ~ v6_orders_2(X3,sK0) )
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f183,plain,
    ( ~ spl5_9
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl5_9
    | spl5_10 ),
    inference(subsumption_resolution,[],[f181,f26])).

fof(f181,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl5_9
    | spl5_10 ),
    inference(subsumption_resolution,[],[f180,f161])).

fof(f161,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl5_9
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f180,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v3_orders_2(sK0)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f179,f25])).

fof(f179,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v3_orders_2(sK0)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f178,f24])).

fof(f178,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v3_orders_2(sK0)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f176,f28])).

fof(f176,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v3_orders_2(sK0)
    | spl5_10 ),
    inference(resolution,[],[f166,f32])).

fof(f166,plain,
    ( ~ v6_orders_2(sK4(sK0,sK2,sK1),sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_10
  <=> v6_orders_2(sK4(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f173,plain,
    ( ~ spl5_2
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | ~ spl5_2
    | spl5_9 ),
    inference(subsumption_resolution,[],[f171,f50])).

fof(f171,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f170,f28])).

fof(f170,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f169,f24])).

fof(f169,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f168,f25])).

fof(f168,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | spl5_9 ),
    inference(resolution,[],[f162,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

% (16841)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f162,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f167,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f158,f45,f164,f160])).

fof(f158,plain,
    ( ~ v6_orders_2(sK4(sK0,sK2,sK1),sK0)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f157,f26])).

fof(f157,plain,
    ( ~ v6_orders_2(sK4(sK0,sK2,sK1),sK0)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v3_orders_2(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f156,f24])).

fof(f156,plain,
    ( ~ v6_orders_2(sK4(sK0,sK2,sK1),sK0)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f155,f28])).

fof(f155,plain,
    ( ~ v6_orders_2(sK4(sK0,sK2,sK1),sK0)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f154,f25])).

fof(f154,plain,
    ( ~ v6_orders_2(sK4(sK0,sK2,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( ~ v6_orders_2(sK4(sK0,sK2,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v3_orders_2(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f146,f35])).

fof(f146,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK1,sK4(sK0,sK2,X2))
        | ~ v6_orders_2(sK4(sK0,sK2,X2),sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK2) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f145,f26])).

fof(f145,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK1,sK4(sK0,sK2,X2))
        | ~ v6_orders_2(sK4(sK0,sK2,X2),sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK2)
        | ~ v3_orders_2(sK0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f144,f28])).

fof(f144,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK1,sK4(sK0,sK2,X2))
        | ~ v6_orders_2(sK4(sK0,sK2,X2),sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK2)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f138,f24])).

fof(f138,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK1,sK4(sK0,sK2,X2))
        | ~ v6_orders_2(sK4(sK0,sK2,X2),sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK2)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK1,sK4(sK0,sK2,X2))
        | ~ v6_orders_2(sK4(sK0,sK2,X2),sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK2)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK2)
        | ~ v3_orders_2(sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f130,f34])).

fof(f114,plain,
    ( spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f110,f107])).

fof(f107,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f99,f106])).

fof(f106,plain,
    ( sK1 = sK2
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f105,f49])).

fof(f49,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f105,plain,
    ( sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f104,f28])).

fof(f104,plain,
    ( ~ l1_orders_2(sK0)
    | sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f103,f24])).

fof(f103,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f102,f25])).

fof(f102,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f99,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f98,f25])).

fof(f98,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f97,f60])).

fof(f60,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_4
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f97,plain,
    ( ~ r2_hidden(sK2,sK3)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_3
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f96,f65])).

fof(f65,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_5
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f96,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK2,sK3)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_3
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f89,f24])).

fof(f89,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK2,sK3)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_3
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f88,f54])).

fof(f54,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X1,sK3)
        | r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f87,f26])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X1,sK3)
        | r1_orders_2(sK0,X0,X1)
        | r1_orders_2(sK0,X1,X0) )
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f86,f75])).

fof(f75,plain,
    ( v6_orders_2(sK3,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_7
  <=> v6_orders_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v6_orders_2(sK3,sK0)
        | ~ v3_orders_2(sK0)
        | ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X1,sK3)
        | r1_orders_2(sK0,X0,X1)
        | r1_orders_2(sK0,X1,X0) )
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f85,f28])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v6_orders_2(sK3,sK0)
        | ~ v3_orders_2(sK0)
        | ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X1,sK3)
        | r1_orders_2(sK0,X0,X1)
        | r1_orders_2(sK0,X1,X0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f70,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v6_orders_2(X4,X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X2,X4)
      | r1_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f70,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f110,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f54,f106])).

fof(f76,plain,
    ( spl5_7
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f18,f52,f48,f73])).

fof(f18,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_orders_2(sK0,sK1,sK2)
    | v6_orders_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f71,plain,
    ( spl5_6
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f19,f52,f48,f68])).

fof(f19,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_orders_2(sK0,sK1,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,
    ( spl5_5
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f20,f52,f48,f63])).

fof(f20,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,
    ( spl5_4
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f21,f52,f48,f58])).

fof(f21,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,
    ( spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f22,f52,f48,f45])).

fof(f22,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,sK2,sK1)
      | ~ r2_orders_2(sK0,sK1,sK2)
      | ~ v6_orders_2(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X3)
      | ~ r2_hidden(sK2,X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,
    ( spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f23,f52,f48,f45])).

fof(f23,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,sK2,sK1)
      | r2_orders_2(sK0,sK1,sK2)
      | ~ v6_orders_2(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X3)
      | ~ r2_hidden(sK2,X3) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (816119809)
% 0.13/0.37  ipcrm: permission denied for id (816152581)
% 0.13/0.38  ipcrm: permission denied for id (816250894)
% 0.13/0.40  ipcrm: permission denied for id (816349211)
% 0.13/0.41  ipcrm: permission denied for id (816381986)
% 0.13/0.42  ipcrm: permission denied for id (816414759)
% 0.13/0.42  ipcrm: permission denied for id (816447530)
% 0.19/0.44  ipcrm: permission denied for id (816611381)
% 0.19/0.46  ipcrm: permission denied for id (816742469)
% 0.19/0.47  ipcrm: permission denied for id (816775238)
% 0.19/0.47  ipcrm: permission denied for id (816840777)
% 0.19/0.47  ipcrm: permission denied for id (816873547)
% 0.19/0.50  ipcrm: permission denied for id (816971870)
% 0.19/0.50  ipcrm: permission denied for id (817004640)
% 0.19/0.50  ipcrm: permission denied for id (817070181)
% 0.19/0.51  ipcrm: permission denied for id (817135719)
% 0.19/0.52  ipcrm: permission denied for id (817332347)
% 0.19/0.52  ipcrm: permission denied for id (817397885)
% 0.65/0.61  % (16837)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.65/0.63  % (16826)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.03/0.63  % (16830)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.03/0.64  % (16833)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.03/0.64  % (16827)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.03/0.65  % (16839)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.14/0.65  % (16826)Refutation found. Thanks to Tanya!
% 1.14/0.65  % SZS status Theorem for theBenchmark
% 1.14/0.65  % SZS output start Proof for theBenchmark
% 1.14/0.65  fof(f224,plain,(
% 1.14/0.65    $false),
% 1.14/0.65    inference(avatar_sat_refutation,[],[f55,f56,f61,f66,f71,f76,f114,f167,f173,f183,f202,f217,f223])).
% 1.14/0.65  fof(f223,plain,(
% 1.14/0.65    ~spl5_2 | ~spl5_3),
% 1.14/0.65    inference(avatar_contradiction_clause,[],[f222])).
% 1.14/0.65  fof(f222,plain,(
% 1.14/0.65    $false | (~spl5_2 | ~spl5_3)),
% 1.14/0.65    inference(subsumption_resolution,[],[f50,f221])).
% 1.14/0.65  fof(f221,plain,(
% 1.14/0.65    ~r2_orders_2(sK0,sK1,sK2) | ~spl5_3),
% 1.14/0.65    inference(subsumption_resolution,[],[f220,f27])).
% 1.14/0.65  fof(f27,plain,(
% 1.14/0.65    v5_orders_2(sK0)),
% 1.14/0.65    inference(cnf_transformation,[],[f8])).
% 1.14/0.65  fof(f8,plain,(
% 1.14/0.65    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <~> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.14/0.65    inference(flattening,[],[f7])).
% 1.14/0.65  fof(f7,plain,(
% 1.14/0.65    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <~> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 1.14/0.65    inference(ennf_transformation,[],[f5])).
% 1.14/0.65  fof(f5,negated_conjecture,(
% 1.14/0.65    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <=> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))))))),
% 1.14/0.65    inference(negated_conjecture,[],[f4])).
% 1.14/0.65  % (16837)Refutation not found, incomplete strategy% (16837)------------------------------
% 1.14/0.65  % (16837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.65  % (16837)Termination reason: Refutation not found, incomplete strategy
% 1.14/0.65  
% 1.14/0.65  % (16837)Memory used [KB]: 6652
% 1.14/0.65  % (16837)Time elapsed: 0.063 s
% 1.14/0.65  % (16837)------------------------------
% 1.14/0.65  % (16837)------------------------------
% 1.14/0.65  % (16831)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.14/0.65  % (16843)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.14/0.66  fof(f4,conjecture,(
% 1.14/0.66    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <=> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))))))),
% 1.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_orders_2)).
% 1.14/0.66  fof(f220,plain,(
% 1.14/0.66    ~v5_orders_2(sK0) | ~r2_orders_2(sK0,sK1,sK2) | ~spl5_3),
% 1.14/0.66    inference(subsumption_resolution,[],[f219,f25])).
% 1.14/0.66  fof(f25,plain,(
% 1.14/0.66    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.14/0.66    inference(cnf_transformation,[],[f8])).
% 1.14/0.66  fof(f219,plain,(
% 1.14/0.66    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r2_orders_2(sK0,sK1,sK2) | ~spl5_3),
% 1.14/0.66    inference(subsumption_resolution,[],[f218,f24])).
% 1.14/0.66  fof(f24,plain,(
% 1.14/0.66    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.14/0.66    inference(cnf_transformation,[],[f8])).
% 1.14/0.66  fof(f218,plain,(
% 1.14/0.66    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r2_orders_2(sK0,sK1,sK2) | ~spl5_3),
% 1.14/0.66    inference(subsumption_resolution,[],[f203,f28])).
% 1.14/0.66  fof(f28,plain,(
% 1.14/0.66    l1_orders_2(sK0)),
% 1.14/0.66    inference(cnf_transformation,[],[f8])).
% 1.14/0.66  fof(f203,plain,(
% 1.14/0.66    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r2_orders_2(sK0,sK1,sK2) | ~spl5_3),
% 1.14/0.66    inference(resolution,[],[f53,f41])).
% 1.14/0.66  fof(f41,plain,(
% 1.14/0.66    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_orders_2(X0,X2,X1)) )),
% 1.14/0.66    inference(cnf_transformation,[],[f13])).
% 1.14/0.66  fof(f13,plain,(
% 1.14/0.66    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.14/0.66    inference(flattening,[],[f12])).
% 1.14/0.66  fof(f12,plain,(
% 1.14/0.66    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.14/0.66    inference(ennf_transformation,[],[f2])).
% 1.14/0.66  fof(f2,axiom,(
% 1.14/0.66    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)))))),
% 1.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).
% 1.14/0.66  fof(f53,plain,(
% 1.14/0.66    r1_orders_2(sK0,sK2,sK1) | ~spl5_3),
% 1.14/0.66    inference(avatar_component_clause,[],[f52])).
% 1.14/0.66  fof(f52,plain,(
% 1.14/0.66    spl5_3 <=> r1_orders_2(sK0,sK2,sK1)),
% 1.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.14/0.66  fof(f50,plain,(
% 1.14/0.66    r2_orders_2(sK0,sK1,sK2) | ~spl5_2),
% 1.14/0.66    inference(avatar_component_clause,[],[f48])).
% 1.14/0.66  fof(f48,plain,(
% 1.14/0.66    spl5_2 <=> r2_orders_2(sK0,sK1,sK2)),
% 1.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.14/0.66  fof(f217,plain,(
% 1.14/0.66    ~spl5_3 | spl5_11),
% 1.14/0.66    inference(avatar_contradiction_clause,[],[f216])).
% 1.14/0.66  fof(f216,plain,(
% 1.14/0.66    $false | (~spl5_3 | spl5_11)),
% 1.14/0.66    inference(subsumption_resolution,[],[f215,f26])).
% 1.14/0.66  fof(f26,plain,(
% 1.14/0.66    v3_orders_2(sK0)),
% 1.14/0.66    inference(cnf_transformation,[],[f8])).
% 1.14/0.66  fof(f215,plain,(
% 1.14/0.66    ~v3_orders_2(sK0) | (~spl5_3 | spl5_11)),
% 1.14/0.66    inference(subsumption_resolution,[],[f214,f53])).
% 1.14/0.66  fof(f214,plain,(
% 1.14/0.66    ~r1_orders_2(sK0,sK2,sK1) | ~v3_orders_2(sK0) | spl5_11),
% 1.14/0.66    inference(subsumption_resolution,[],[f213,f24])).
% 1.14/0.66  fof(f213,plain,(
% 1.14/0.66    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | ~v3_orders_2(sK0) | spl5_11),
% 1.14/0.66    inference(subsumption_resolution,[],[f212,f25])).
% 1.14/0.66  fof(f212,plain,(
% 1.14/0.66    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | ~v3_orders_2(sK0) | spl5_11),
% 1.14/0.66    inference(subsumption_resolution,[],[f210,f28])).
% 1.14/0.66  fof(f210,plain,(
% 1.14/0.66    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | ~v3_orders_2(sK0) | spl5_11),
% 1.14/0.66    inference(resolution,[],[f196,f32])).
% 1.14/0.66  fof(f32,plain,(
% 1.14/0.66    ( ! [X2,X0,X1] : (v6_orders_2(sK4(X0,X1,X2),X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0)) )),
% 1.14/0.66    inference(cnf_transformation,[],[f11])).
% 1.14/0.66  fof(f11,plain,(
% 1.14/0.66    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 1.14/0.66    inference(flattening,[],[f10])).
% 1.14/0.66  fof(f10,plain,(
% 1.14/0.66    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : ((r2_hidden(X2,X3) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0))) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.14/0.66    inference(ennf_transformation,[],[f6])).
% 1.14/0.66  fof(f6,plain,(
% 1.14/0.66    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0)))))))),
% 1.14/0.66    inference(rectify,[],[f3])).
% 1.14/0.66  fof(f3,axiom,(
% 1.14/0.66    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))))))),
% 1.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).
% 1.14/0.66  fof(f196,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK1,sK2),sK0) | spl5_11),
% 1.14/0.66    inference(avatar_component_clause,[],[f194])).
% 1.14/0.66  fof(f194,plain,(
% 1.14/0.66    spl5_11 <=> v6_orders_2(sK4(sK0,sK1,sK2),sK0)),
% 1.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.14/0.66  fof(f202,plain,(
% 1.14/0.66    ~spl5_3 | ~spl5_11 | ~spl5_1),
% 1.14/0.66    inference(avatar_split_clause,[],[f201,f45,f194,f52])).
% 1.14/0.66  fof(f45,plain,(
% 1.14/0.66    spl5_1 <=> ! [X3] : (~v6_orders_2(X3,sK0) | ~r2_hidden(sK2,X3) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.14/0.66  fof(f201,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK1,sK2),sK0) | ~r1_orders_2(sK0,sK2,sK1) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f200,f26])).
% 1.14/0.66  fof(f200,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK1,sK2),sK0) | ~r1_orders_2(sK0,sK2,sK1) | ~v3_orders_2(sK0) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f199,f24])).
% 1.14/0.66  fof(f199,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK1,sK2),sK0) | ~r1_orders_2(sK0,sK2,sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f198,f28])).
% 1.14/0.66  fof(f198,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK1,sK2),sK0) | ~r1_orders_2(sK0,sK2,sK1) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f150,f25])).
% 1.14/0.66  fof(f150,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK1,sK2),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~spl5_1),
% 1.14/0.66    inference(duplicate_literal_removal,[],[f147])).
% 1.14/0.66  fof(f147,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK1,sK2),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | ~v3_orders_2(sK0) | ~spl5_1),
% 1.14/0.66    inference(resolution,[],[f143,f34])).
% 1.14/0.66  fof(f34,plain,(
% 1.14/0.66    ( ! [X2,X0,X1] : (r2_hidden(X1,sK4(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0)) )),
% 1.14/0.66    inference(cnf_transformation,[],[f11])).
% 1.14/0.66  fof(f143,plain,(
% 1.14/0.66    ( ! [X0] : (~r2_hidden(sK1,sK4(sK0,X0,sK2)) | ~v6_orders_2(sK4(sK0,X0,sK2),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0)) ) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f142,f26])).
% 1.14/0.66  fof(f142,plain,(
% 1.14/0.66    ( ! [X0] : (~r2_hidden(sK1,sK4(sK0,X0,sK2)) | ~v6_orders_2(sK4(sK0,X0,sK2),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | ~v3_orders_2(sK0)) ) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f141,f28])).
% 1.14/0.66  fof(f141,plain,(
% 1.14/0.66    ( ! [X0] : (~r2_hidden(sK1,sK4(sK0,X0,sK2)) | ~v6_orders_2(sK4(sK0,X0,sK2),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)) ) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f140,f24])).
% 1.14/0.66  fof(f140,plain,(
% 1.14/0.66    ( ! [X0] : (~r2_hidden(sK1,sK4(sK0,X0,sK2)) | ~v6_orders_2(sK4(sK0,X0,sK2),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)) ) | ~spl5_1),
% 1.14/0.66    inference(duplicate_literal_removal,[],[f133])).
% 1.14/0.66  fof(f133,plain,(
% 1.14/0.66    ( ! [X0] : (~r2_hidden(sK1,sK4(sK0,X0,sK2)) | ~v6_orders_2(sK4(sK0,X0,sK2),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | ~v3_orders_2(sK0)) ) | ~spl5_1),
% 1.14/0.66    inference(resolution,[],[f130,f35])).
% 1.14/0.66  fof(f35,plain,(
% 1.14/0.66    ( ! [X2,X0,X1] : (r2_hidden(X2,sK4(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0)) )),
% 1.14/0.66    inference(cnf_transformation,[],[f11])).
% 1.14/0.66  fof(f130,plain,(
% 1.14/0.66    ( ! [X0,X1] : (~r2_hidden(sK2,sK4(sK0,X0,X1)) | ~r2_hidden(sK1,sK4(sK0,X0,X1)) | ~v6_orders_2(sK4(sK0,X0,X1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0)) ) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f129,f26])).
% 1.14/0.66  fof(f129,plain,(
% 1.14/0.66    ( ! [X0,X1] : (~r2_hidden(sK2,sK4(sK0,X0,X1)) | ~r2_hidden(sK1,sK4(sK0,X0,X1)) | ~v6_orders_2(sK4(sK0,X0,X1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~v3_orders_2(sK0)) ) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f123,f28])).
% 1.14/0.66  fof(f123,plain,(
% 1.14/0.66    ( ! [X0,X1] : (~r2_hidden(sK2,sK4(sK0,X0,X1)) | ~r2_hidden(sK1,sK4(sK0,X0,X1)) | ~v6_orders_2(sK4(sK0,X0,X1),sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~v3_orders_2(sK0)) ) | ~spl5_1),
% 1.14/0.66    inference(resolution,[],[f46,f33])).
% 1.14/0.66  fof(f33,plain,(
% 1.14/0.66    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0)) )),
% 1.14/0.66    inference(cnf_transformation,[],[f11])).
% 1.14/0.66  fof(f46,plain,(
% 1.14/0.66    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,X3) | ~r2_hidden(sK1,X3) | ~v6_orders_2(X3,sK0)) ) | ~spl5_1),
% 1.14/0.66    inference(avatar_component_clause,[],[f45])).
% 1.14/0.66  fof(f183,plain,(
% 1.14/0.66    ~spl5_9 | spl5_10),
% 1.14/0.66    inference(avatar_contradiction_clause,[],[f182])).
% 1.14/0.66  fof(f182,plain,(
% 1.14/0.66    $false | (~spl5_9 | spl5_10)),
% 1.14/0.66    inference(subsumption_resolution,[],[f181,f26])).
% 1.14/0.66  fof(f181,plain,(
% 1.14/0.66    ~v3_orders_2(sK0) | (~spl5_9 | spl5_10)),
% 1.14/0.66    inference(subsumption_resolution,[],[f180,f161])).
% 1.14/0.66  fof(f161,plain,(
% 1.14/0.66    r1_orders_2(sK0,sK1,sK2) | ~spl5_9),
% 1.14/0.66    inference(avatar_component_clause,[],[f160])).
% 1.14/0.66  fof(f160,plain,(
% 1.14/0.66    spl5_9 <=> r1_orders_2(sK0,sK1,sK2)),
% 1.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.14/0.66  fof(f180,plain,(
% 1.14/0.66    ~r1_orders_2(sK0,sK1,sK2) | ~v3_orders_2(sK0) | spl5_10),
% 1.14/0.66    inference(subsumption_resolution,[],[f179,f25])).
% 1.14/0.66  fof(f179,plain,(
% 1.14/0.66    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | ~v3_orders_2(sK0) | spl5_10),
% 1.14/0.66    inference(subsumption_resolution,[],[f178,f24])).
% 1.14/0.66  fof(f178,plain,(
% 1.14/0.66    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | ~v3_orders_2(sK0) | spl5_10),
% 1.14/0.66    inference(subsumption_resolution,[],[f176,f28])).
% 1.14/0.66  fof(f176,plain,(
% 1.14/0.66    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | ~v3_orders_2(sK0) | spl5_10),
% 1.14/0.66    inference(resolution,[],[f166,f32])).
% 1.14/0.66  fof(f166,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK2,sK1),sK0) | spl5_10),
% 1.14/0.66    inference(avatar_component_clause,[],[f164])).
% 1.14/0.66  fof(f164,plain,(
% 1.14/0.66    spl5_10 <=> v6_orders_2(sK4(sK0,sK2,sK1),sK0)),
% 1.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.14/0.66  fof(f173,plain,(
% 1.14/0.66    ~spl5_2 | spl5_9),
% 1.14/0.66    inference(avatar_contradiction_clause,[],[f172])).
% 1.14/0.66  fof(f172,plain,(
% 1.14/0.66    $false | (~spl5_2 | spl5_9)),
% 1.14/0.66    inference(subsumption_resolution,[],[f171,f50])).
% 1.14/0.66  fof(f171,plain,(
% 1.14/0.66    ~r2_orders_2(sK0,sK1,sK2) | spl5_9),
% 1.14/0.66    inference(subsumption_resolution,[],[f170,f28])).
% 1.14/0.66  fof(f170,plain,(
% 1.14/0.66    ~l1_orders_2(sK0) | ~r2_orders_2(sK0,sK1,sK2) | spl5_9),
% 1.14/0.66    inference(subsumption_resolution,[],[f169,f24])).
% 1.14/0.66  fof(f169,plain,(
% 1.14/0.66    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r2_orders_2(sK0,sK1,sK2) | spl5_9),
% 1.14/0.66    inference(subsumption_resolution,[],[f168,f25])).
% 1.14/0.66  fof(f168,plain,(
% 1.14/0.66    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r2_orders_2(sK0,sK1,sK2) | spl5_9),
% 1.14/0.66    inference(resolution,[],[f162,f29])).
% 1.14/0.66  fof(f29,plain,(
% 1.14/0.66    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_orders_2(X0,X1,X2)) )),
% 1.14/0.66    inference(cnf_transformation,[],[f9])).
% 1.14/0.66  % (16841)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.14/0.66  fof(f9,plain,(
% 1.14/0.66    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.14/0.66    inference(ennf_transformation,[],[f1])).
% 1.14/0.66  fof(f1,axiom,(
% 1.14/0.66    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.14/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 1.14/0.66  fof(f162,plain,(
% 1.14/0.66    ~r1_orders_2(sK0,sK1,sK2) | spl5_9),
% 1.14/0.66    inference(avatar_component_clause,[],[f160])).
% 1.14/0.66  fof(f167,plain,(
% 1.14/0.66    ~spl5_9 | ~spl5_10 | ~spl5_1),
% 1.14/0.66    inference(avatar_split_clause,[],[f158,f45,f164,f160])).
% 1.14/0.66  fof(f158,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK2,sK1),sK0) | ~r1_orders_2(sK0,sK1,sK2) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f157,f26])).
% 1.14/0.66  fof(f157,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK2,sK1),sK0) | ~r1_orders_2(sK0,sK1,sK2) | ~v3_orders_2(sK0) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f156,f24])).
% 1.14/0.66  fof(f156,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK2,sK1),sK0) | ~r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f155,f28])).
% 1.14/0.66  fof(f155,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK2,sK1),sK0) | ~r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f154,f25])).
% 1.14/0.66  fof(f154,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK2,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~spl5_1),
% 1.14/0.66    inference(duplicate_literal_removal,[],[f151])).
% 1.14/0.66  fof(f151,plain,(
% 1.14/0.66    ~v6_orders_2(sK4(sK0,sK2,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | ~v3_orders_2(sK0) | ~spl5_1),
% 1.14/0.66    inference(resolution,[],[f146,f35])).
% 1.14/0.66  fof(f146,plain,(
% 1.14/0.66    ( ! [X2] : (~r2_hidden(sK1,sK4(sK0,sK2,X2)) | ~v6_orders_2(sK4(sK0,sK2,X2),sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK2)) ) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f145,f26])).
% 1.14/0.66  fof(f145,plain,(
% 1.14/0.66    ( ! [X2] : (~r2_hidden(sK1,sK4(sK0,sK2,X2)) | ~v6_orders_2(sK4(sK0,sK2,X2),sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK2) | ~v3_orders_2(sK0)) ) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f144,f28])).
% 1.14/0.66  fof(f144,plain,(
% 1.14/0.66    ( ! [X2] : (~r2_hidden(sK1,sK4(sK0,sK2,X2)) | ~v6_orders_2(sK4(sK0,sK2,X2),sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK2) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)) ) | ~spl5_1),
% 1.14/0.66    inference(subsumption_resolution,[],[f138,f24])).
% 1.14/0.66  fof(f138,plain,(
% 1.14/0.66    ( ! [X2] : (~r2_hidden(sK1,sK4(sK0,sK2,X2)) | ~v6_orders_2(sK4(sK0,sK2,X2),sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK2) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)) ) | ~spl5_1),
% 1.14/0.66    inference(duplicate_literal_removal,[],[f135])).
% 1.14/0.66  fof(f135,plain,(
% 1.14/0.66    ( ! [X2] : (~r2_hidden(sK1,sK4(sK0,sK2,X2)) | ~v6_orders_2(sK4(sK0,sK2,X2),sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK2) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK2) | ~v3_orders_2(sK0)) ) | ~spl5_1),
% 1.14/0.66    inference(resolution,[],[f130,f34])).
% 1.14/0.66  fof(f114,plain,(
% 1.14/0.66    spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7),
% 1.14/0.66    inference(avatar_contradiction_clause,[],[f113])).
% 1.14/0.66  fof(f113,plain,(
% 1.14/0.66    $false | (spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(subsumption_resolution,[],[f110,f107])).
% 1.14/0.66  fof(f107,plain,(
% 1.14/0.66    r1_orders_2(sK0,sK1,sK1) | (spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(backward_demodulation,[],[f99,f106])).
% 1.14/0.66  fof(f106,plain,(
% 1.14/0.66    sK1 = sK2 | (spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(subsumption_resolution,[],[f105,f49])).
% 1.14/0.66  fof(f49,plain,(
% 1.14/0.66    ~r2_orders_2(sK0,sK1,sK2) | spl5_2),
% 1.14/0.66    inference(avatar_component_clause,[],[f48])).
% 1.14/0.66  fof(f105,plain,(
% 1.14/0.66    sK1 = sK2 | r2_orders_2(sK0,sK1,sK2) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(subsumption_resolution,[],[f104,f28])).
% 1.14/0.66  fof(f104,plain,(
% 1.14/0.66    ~l1_orders_2(sK0) | sK1 = sK2 | r2_orders_2(sK0,sK1,sK2) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(subsumption_resolution,[],[f103,f24])).
% 1.14/0.66  fof(f103,plain,(
% 1.14/0.66    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK1 = sK2 | r2_orders_2(sK0,sK1,sK2) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(subsumption_resolution,[],[f102,f25])).
% 1.14/0.66  fof(f102,plain,(
% 1.14/0.66    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK1 = sK2 | r2_orders_2(sK0,sK1,sK2) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(resolution,[],[f99,f31])).
% 1.14/0.66  fof(f31,plain,(
% 1.14/0.66    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2 | r2_orders_2(X0,X1,X2)) )),
% 1.14/0.66    inference(cnf_transformation,[],[f9])).
% 1.14/0.66  fof(f99,plain,(
% 1.14/0.66    r1_orders_2(sK0,sK1,sK2) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(subsumption_resolution,[],[f98,f25])).
% 1.14/0.66  fof(f98,plain,(
% 1.14/0.66    r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(subsumption_resolution,[],[f97,f60])).
% 1.14/0.66  fof(f60,plain,(
% 1.14/0.66    r2_hidden(sK2,sK3) | ~spl5_4),
% 1.14/0.66    inference(avatar_component_clause,[],[f58])).
% 1.14/0.66  fof(f58,plain,(
% 1.14/0.66    spl5_4 <=> r2_hidden(sK2,sK3)),
% 1.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.14/0.66  fof(f97,plain,(
% 1.14/0.66    ~r2_hidden(sK2,sK3) | r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl5_3 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(subsumption_resolution,[],[f96,f65])).
% 1.14/0.66  fof(f65,plain,(
% 1.14/0.66    r2_hidden(sK1,sK3) | ~spl5_5),
% 1.14/0.66    inference(avatar_component_clause,[],[f63])).
% 1.14/0.66  fof(f63,plain,(
% 1.14/0.66    spl5_5 <=> r2_hidden(sK1,sK3)),
% 1.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.14/0.66  fof(f96,plain,(
% 1.14/0.66    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK2,sK3) | r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl5_3 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(subsumption_resolution,[],[f89,f24])).
% 1.14/0.66  fof(f89,plain,(
% 1.14/0.66    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK3) | ~r2_hidden(sK2,sK3) | r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl5_3 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(resolution,[],[f88,f54])).
% 1.14/0.66  fof(f54,plain,(
% 1.14/0.66    ~r1_orders_2(sK0,sK2,sK1) | spl5_3),
% 1.14/0.66    inference(avatar_component_clause,[],[f52])).
% 1.14/0.66  fof(f88,plain,(
% 1.14/0.66    ( ! [X0,X1] : (r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK3) | r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(subsumption_resolution,[],[f87,f26])).
% 1.14/0.66  fof(f87,plain,(
% 1.14/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK3) | r1_orders_2(sK0,X0,X1) | r1_orders_2(sK0,X1,X0)) ) | (~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(subsumption_resolution,[],[f86,f75])).
% 1.14/0.66  fof(f75,plain,(
% 1.14/0.66    v6_orders_2(sK3,sK0) | ~spl5_7),
% 1.14/0.66    inference(avatar_component_clause,[],[f73])).
% 1.14/0.66  fof(f73,plain,(
% 1.14/0.66    spl5_7 <=> v6_orders_2(sK3,sK0)),
% 1.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.14/0.66  fof(f86,plain,(
% 1.14/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v6_orders_2(sK3,sK0) | ~v3_orders_2(sK0) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK3) | r1_orders_2(sK0,X0,X1) | r1_orders_2(sK0,X1,X0)) ) | ~spl5_6),
% 1.14/0.66    inference(subsumption_resolution,[],[f85,f28])).
% 1.14/0.66  fof(f85,plain,(
% 1.14/0.66    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v6_orders_2(sK3,sK0) | ~v3_orders_2(sK0) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK3) | r1_orders_2(sK0,X0,X1) | r1_orders_2(sK0,X1,X0)) ) | ~spl5_6),
% 1.14/0.66    inference(resolution,[],[f70,f40])).
% 1.14/0.66  fof(f40,plain,(
% 1.14/0.66    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v6_orders_2(X4,X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,X4) | ~r2_hidden(X2,X4) | r1_orders_2(X0,X1,X2) | r1_orders_2(X0,X2,X1)) )),
% 1.14/0.66    inference(cnf_transformation,[],[f11])).
% 1.14/0.66  fof(f70,plain,(
% 1.14/0.66    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_6),
% 1.14/0.66    inference(avatar_component_clause,[],[f68])).
% 1.14/0.66  fof(f68,plain,(
% 1.14/0.66    spl5_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.14/0.66  fof(f110,plain,(
% 1.14/0.66    ~r1_orders_2(sK0,sK1,sK1) | (spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 1.14/0.66    inference(backward_demodulation,[],[f54,f106])).
% 1.14/0.66  fof(f76,plain,(
% 1.14/0.66    spl5_7 | spl5_2 | spl5_3),
% 1.14/0.66    inference(avatar_split_clause,[],[f18,f52,f48,f73])).
% 1.14/0.66  fof(f18,plain,(
% 1.14/0.66    r1_orders_2(sK0,sK2,sK1) | r2_orders_2(sK0,sK1,sK2) | v6_orders_2(sK3,sK0)),
% 1.14/0.66    inference(cnf_transformation,[],[f8])).
% 1.14/0.66  fof(f71,plain,(
% 1.14/0.66    spl5_6 | spl5_2 | spl5_3),
% 1.14/0.66    inference(avatar_split_clause,[],[f19,f52,f48,f68])).
% 1.14/0.66  fof(f19,plain,(
% 1.14/0.66    r1_orders_2(sK0,sK2,sK1) | r2_orders_2(sK0,sK1,sK2) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.14/0.66    inference(cnf_transformation,[],[f8])).
% 1.14/0.66  fof(f66,plain,(
% 1.14/0.66    spl5_5 | spl5_2 | spl5_3),
% 1.14/0.66    inference(avatar_split_clause,[],[f20,f52,f48,f63])).
% 1.14/0.66  fof(f20,plain,(
% 1.14/0.66    r1_orders_2(sK0,sK2,sK1) | r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,sK3)),
% 1.14/0.66    inference(cnf_transformation,[],[f8])).
% 1.14/0.66  fof(f61,plain,(
% 1.14/0.66    spl5_4 | spl5_2 | spl5_3),
% 1.14/0.66    inference(avatar_split_clause,[],[f21,f52,f48,f58])).
% 1.14/0.66  fof(f21,plain,(
% 1.14/0.66    r1_orders_2(sK0,sK2,sK1) | r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK2,sK3)),
% 1.14/0.66    inference(cnf_transformation,[],[f8])).
% 1.14/0.66  fof(f56,plain,(
% 1.14/0.66    spl5_1 | ~spl5_2 | spl5_3),
% 1.14/0.66    inference(avatar_split_clause,[],[f22,f52,f48,f45])).
% 1.14/0.66  fof(f22,plain,(
% 1.14/0.66    ( ! [X3] : (r1_orders_2(sK0,sK2,sK1) | ~r2_orders_2(sK0,sK1,sK2) | ~v6_orders_2(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~r2_hidden(sK2,X3)) )),
% 1.14/0.66    inference(cnf_transformation,[],[f8])).
% 1.14/0.66  fof(f55,plain,(
% 1.14/0.66    spl5_1 | spl5_2 | ~spl5_3),
% 1.14/0.66    inference(avatar_split_clause,[],[f23,f52,f48,f45])).
% 1.14/0.66  fof(f23,plain,(
% 1.14/0.66    ( ! [X3] : (~r1_orders_2(sK0,sK2,sK1) | r2_orders_2(sK0,sK1,sK2) | ~v6_orders_2(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~r2_hidden(sK2,X3)) )),
% 1.14/0.66    inference(cnf_transformation,[],[f8])).
% 1.14/0.66  % SZS output end Proof for theBenchmark
% 1.14/0.66  % (16826)------------------------------
% 1.14/0.66  % (16826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.66  % (16826)Termination reason: Refutation
% 1.14/0.66  
% 1.14/0.66  % (16826)Memory used [KB]: 10618
% 1.14/0.66  % (16826)Time elapsed: 0.068 s
% 1.14/0.66  % (16826)------------------------------
% 1.14/0.66  % (16826)------------------------------
% 1.14/0.66  % (16838)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.14/0.66  % (16665)Success in time 0.305 s
%------------------------------------------------------------------------------
