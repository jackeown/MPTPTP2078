%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 214 expanded)
%              Number of leaves         :   32 (  92 expanded)
%              Depth                    :   10
%              Number of atoms          :  551 ( 924 expanded)
%              Number of equality atoms :   53 (  98 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (9897)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f74,f78,f82,f86,f90,f98,f105,f117,f121,f127,f135,f142,f146,f159,f184,f191,f210,f214])).

fof(f214,plain,
    ( ~ spl3_6
    | ~ spl3_8
    | ~ spl3_14
    | spl3_19
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_14
    | spl3_19
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f69,f77,f126,f104,f209])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl3_32
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f104,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_14
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f126,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_19
  <=> k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f77,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_8
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f69,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f210,plain,
    ( spl3_32
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f199,f189,f140,f64,f60,f56,f52,f48,f208])).

fof(f48,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f52,plain,
    ( spl3_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f56,plain,
    ( spl3_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f60,plain,
    ( spl3_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f64,plain,
    ( spl3_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f140,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f189,plain,
    ( spl3_30
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f198,f49])).

fof(f49,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f197,f65])).

fof(f65,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f196,f61])).

fof(f61,plain,
    ( v5_orders_2(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f195,f57])).

fof(f57,plain,
    ( v4_orders_2(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f194,f53])).

fof(f53,plain,
    ( v3_orders_2(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(resolution,[],[f190,f141])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f140])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f189])).

fof(f191,plain,
    ( spl3_30
    | ~ spl3_18
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f187,f182,f119,f189])).

fof(f119,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k1_xboole_0 = X1
        | m1_subset_1(sK2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f182,plain,
    ( spl3_29
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2(X2,k3_orders_2(sK0,X1,X0)),X1)
        | ~ m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0)),u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_18
    | ~ spl3_29 ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_18
    | ~ spl3_29 ),
    inference(resolution,[],[f183,f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK2(X0,X1),X0)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f119])).

fof(f183,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2(X2,k3_orders_2(sK0,X1,X0)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(X2)) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f182])).

fof(f184,plain,
    ( spl3_29
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f169,f157,f133,f182])).

fof(f133,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k1_xboole_0 = X1
        | r2_hidden(sK2(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

% (9886)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f157,plain,
    ( spl3_25
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X2)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f169,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2(X2,k3_orders_2(sK0,X1,X0)),X1)
        | ~ m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0)),u1_struct_0(sK0))
        | k1_xboole_0 = k3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(X2)) )
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(resolution,[],[f158,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f133])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f157])).

fof(f159,plain,
    ( spl3_25
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f155,f144,f64,f60,f56,f52,f48,f157])).

fof(f144,plain,
    ( spl3_23
  <=> ! [X1,X3,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(X1,X3)
        | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f155,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X2)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f154,f49])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X2)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f153,f61])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X2)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f152,f57])).

fof(f152,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X2)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f151,f53])).

fof(f151,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,X2)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(resolution,[],[f145,f65])).

fof(f145,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(X1,X3)
        | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f35,f144])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f142,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f43,f140])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f135,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f39,f133])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f127,plain,
    ( ~ spl3_19
    | ~ spl3_5
    | spl3_7
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f123,f115,f72,f64,f125])).

fof(f72,plain,
    ( spl3_7
  <=> k1_xboole_0 = k3_orders_2(sK0,k1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f115,plain,
    ( spl3_17
  <=> ! [X0] :
        ( k1_xboole_0 = k1_struct_0(X0)
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f123,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1)
    | ~ spl3_5
    | spl3_7
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f73,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(resolution,[],[f116,f65])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | k1_xboole_0 = k1_struct_0(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f115])).

fof(f73,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f121,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f38,f119])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | m1_subset_1(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f117,plain,
    ( spl3_17
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f101,f96,f80,f115])).

fof(f80,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ l1_orders_2(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f96,plain,
    ( spl3_13
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k1_xboole_0 = k1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f101,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_struct_0(X0)
        | ~ l1_orders_2(X0) )
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(resolution,[],[f97,f81])).

fof(f81,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_orders_2(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k1_xboole_0 = k1_struct_0(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f96])).

fof(f105,plain,
    ( spl3_14
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f99,f88,f84,f103])).

fof(f84,plain,
    ( spl3_10
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f88,plain,
    ( spl3_11
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f99,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(superposition,[],[f85,f89])).

fof(f89,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f85,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f98,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f32,f96])).

fof(f32,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f90,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f86,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f82,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f78,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f31,f76])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f74,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f25,f72])).

fof(f25,plain,(
    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

fof(f70,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f68])).

fof(f24,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (9891)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.46  % (9898)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (9903)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (9892)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (9903)Refutation not found, incomplete strategy% (9903)------------------------------
% 0.20/0.48  % (9903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9900)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (9883)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (9892)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (9903)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (9903)Memory used [KB]: 10618
% 0.20/0.48  % (9903)Time elapsed: 0.072 s
% 0.20/0.48  % (9903)------------------------------
% 0.20/0.48  % (9903)------------------------------
% 0.20/0.48  % (9895)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (9899)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  % (9897)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f74,f78,f82,f86,f90,f98,f105,f117,f121,f127,f135,f142,f146,f159,f184,f191,f210,f214])).
% 0.20/0.48  fof(f214,plain,(
% 0.20/0.48    ~spl3_6 | ~spl3_8 | ~spl3_14 | spl3_19 | ~spl3_32),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f211])).
% 0.20/0.48  fof(f211,plain,(
% 0.20/0.48    $false | (~spl3_6 | ~spl3_8 | ~spl3_14 | spl3_19 | ~spl3_32)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f69,f77,f126,f104,f209])).
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_32),
% 0.20/0.48    inference(avatar_component_clause,[],[f208])).
% 0.20/0.48  fof(f208,plain,(
% 0.20/0.48    spl3_32 <=> ! [X1,X0] : (r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl3_14 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1) | spl3_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f125])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    spl3_19 <=> k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f76])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl3_8 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f68])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl3_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    spl3_32 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_22 | ~spl3_30),
% 0.20/0.48    inference(avatar_split_clause,[],[f199,f189,f140,f64,f60,f56,f52,f48,f208])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl3_1 <=> v2_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl3_2 <=> v3_orders_2(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    spl3_3 <=> v4_orders_2(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    spl3_4 <=> v5_orders_2(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    spl3_5 <=> l1_orders_2(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    spl3_22 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    spl3_30 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_22 | ~spl3_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f198,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ~v2_struct_0(sK0) | spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f48])).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_22 | ~spl3_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f197,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    l1_orders_2(sK0) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f64])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_22 | ~spl3_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f196,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    v5_orders_2(sK0) | ~spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f60])).
% 0.20/0.48  fof(f196,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_22 | ~spl3_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f195,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    v4_orders_2(sK0) | ~spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f56])).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_22 | ~spl3_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f194,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    v3_orders_2(sK0) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f52])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl3_22 | ~spl3_30)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f192])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl3_22 | ~spl3_30)),
% 0.20/0.48    inference(resolution,[],[f190,f141])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl3_22),
% 0.20/0.48    inference(avatar_component_clause,[],[f140])).
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_30),
% 0.20/0.48    inference(avatar_component_clause,[],[f189])).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    spl3_30 | ~spl3_18 | ~spl3_29),
% 0.20/0.48    inference(avatar_split_clause,[],[f187,f182,f119,f189])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    spl3_18 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1),X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    spl3_29 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(X2,k3_orders_2(sK0,X1,X0)),X1) | ~m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0)),u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X1,X0) | ~m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(X2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_18 | ~spl3_29)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f185])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(u1_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | ~m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_18 | ~spl3_29)),
% 0.20/0.48    inference(resolution,[],[f183,f120])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f119])).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0)),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(X2,k3_orders_2(sK0,X1,X0)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X1,X0) | ~m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(X2))) ) | ~spl3_29),
% 0.20/0.48    inference(avatar_component_clause,[],[f182])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    spl3_29 | ~spl3_21 | ~spl3_25),
% 0.20/0.48    inference(avatar_split_clause,[],[f169,f157,f133,f182])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl3_21 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1),X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.48  % (9886)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    spl3_25 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(X2,k3_orders_2(sK0,X1,X0)),X1) | ~m1_subset_1(sK2(X2,k3_orders_2(sK0,X1,X0)),u1_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,X1,X0) | ~m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(X2))) ) | (~spl3_21 | ~spl3_25)),
% 0.20/0.48    inference(resolution,[],[f158,f134])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_21),
% 0.20/0.48    inference(avatar_component_clause,[],[f133])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl3_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f157])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    spl3_25 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f155,f144,f64,f60,f56,f52,f48,f157])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    spl3_23 <=> ! [X1,X3,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f154,f49])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f153,f61])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f152,f57])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (~spl3_2 | ~spl3_5 | ~spl3_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f151,f53])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X2) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (~spl3_5 | ~spl3_23)),
% 0.20/0.49    inference(resolution,[],[f145,f65])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) ) | ~spl3_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f144])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    spl3_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f144])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    spl3_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f140])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    spl3_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f39,f133])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ~spl3_19 | ~spl3_5 | spl3_7 | ~spl3_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f123,f115,f72,f64,f125])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl3_7 <=> k1_xboole_0 = k3_orders_2(sK0,k1_struct_0(sK0),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl3_17 <=> ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1) | (~spl3_5 | spl3_7 | ~spl3_17)),
% 0.20/0.49    inference(backward_demodulation,[],[f73,f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    k1_xboole_0 = k1_struct_0(sK0) | (~spl3_5 | ~spl3_17)),
% 0.20/0.49    inference(resolution,[],[f116,f65])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_orders_2(X0) | k1_xboole_0 = k1_struct_0(X0)) ) | ~spl3_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f115])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1) | spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f119])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl3_17 | ~spl3_9 | ~spl3_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f101,f96,f80,f115])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl3_9 <=> ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl3_13 <=> ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_orders_2(X0)) ) | (~spl3_9 | ~spl3_13)),
% 0.20/0.49    inference(resolution,[],[f97,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) ) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f80])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) ) | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f96])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl3_14 | ~spl3_10 | ~spl3_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f99,f88,f84,f103])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl3_10 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl3_11 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_10 | ~spl3_11)),
% 0.20/0.49    inference(superposition,[],[f85,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f88])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl3_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f84])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    spl3_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f96])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl3_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f88])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl3_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f84])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f80])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f76])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ~spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f25,f72])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f24,f68])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f64])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    l1_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f60])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    v5_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f28,f56])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    v4_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f27,f52])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    v3_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f48])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (9892)------------------------------
% 0.20/0.49  % (9892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (9892)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (9892)Memory used [KB]: 10746
% 0.20/0.49  % (9892)Time elapsed: 0.080 s
% 0.20/0.49  % (9892)------------------------------
% 0.20/0.49  % (9892)------------------------------
% 0.20/0.49  % (9881)Success in time 0.133 s
%------------------------------------------------------------------------------
