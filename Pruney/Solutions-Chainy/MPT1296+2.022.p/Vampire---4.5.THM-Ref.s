%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 169 expanded)
%              Number of leaves         :   32 (  74 expanded)
%              Depth                    :    7
%              Number of atoms          :  337 ( 489 expanded)
%              Number of equality atoms :   66 ( 105 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f49,f53,f57,f61,f65,f70,f78,f82,f87,f91,f104,f108,f113,f122,f141,f148,f161,f176,f199,f217,f224])).

fof(f224,plain,
    ( ~ spl3_2
    | ~ spl3_12
    | spl3_30 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_12
    | spl3_30 ),
    inference(subsumption_resolution,[],[f220,f48])).

fof(f48,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f220,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_12
    | spl3_30 ),
    inference(resolution,[],[f216,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f216,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl3_30
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f217,plain,
    ( ~ spl3_30
    | ~ spl3_10
    | spl3_27 ),
    inference(avatar_split_clause,[],[f204,f197,f80,f215])).

fof(f80,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f197,plain,
    ( spl3_27
  <=> m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f204,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_10
    | spl3_27 ),
    inference(resolution,[],[f198,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f198,plain,
    ( ~ m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f197])).

fof(f199,plain,
    ( ~ spl3_27
    | spl3_4
    | ~ spl3_9
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f187,f156,f76,f55,f197])).

fof(f55,plain,
    ( spl3_4
  <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f76,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f156,plain,
    ( spl3_23
  <=> k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f187,plain,
    ( ~ m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | spl3_4
    | ~ spl3_9
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f186,f56])).

fof(f56,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

% (12139)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f186,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | ~ m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl3_9
    | ~ spl3_23 ),
    inference(superposition,[],[f77,f157])).

fof(f157,plain,
    ( k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f156])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f176,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f174,f48])).

fof(f174,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_1
    | ~ spl3_3
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f173,f44])).

fof(f44,plain,
    ( k1_xboole_0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f173,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f167,f52])).

fof(f52,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f167,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2(sK1)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(superposition,[],[f140,f160])).

fof(f160,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_24
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f140,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(k7_setfam_1(X6,X5),k3_subset_1(X6,sK2(X5)))
        | k1_xboole_0 = X5
        | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X6))) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_21
  <=> ! [X5,X6] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X6)))
        | k1_xboole_0 = X5
        | ~ r1_tarski(k7_setfam_1(X6,X5),k3_subset_1(X6,sK2(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f161,plain,
    ( spl3_23
    | spl3_24
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f154,f146,f47,f159,f156])).

fof(f146,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( k6_setfam_1(X0,X1) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))
        | k1_xboole_0 = k7_setfam_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f154,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(resolution,[],[f147,f48])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k1_xboole_0 = k7_setfam_1(X0,X1)
        | k6_setfam_1(X0,X1) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1))) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,
    ( spl3_22
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f124,f102,f89,f85,f146])).

fof(f85,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f102,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k1_xboole_0 = X1
        | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( k6_setfam_1(X0,X1) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))
        | k1_xboole_0 = k7_setfam_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f123,f90])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( k6_setfam_1(X0,X1) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))
        | k1_xboole_0 = k7_setfam_1(X0,X1)
        | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(superposition,[],[f103,f86])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f141,plain,
    ( spl3_21
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f130,f120,f59,f139])).

fof(f59,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f120,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
        | r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f130,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X6)))
        | k1_xboole_0 = X5
        | ~ r1_tarski(k7_setfam_1(X6,X5),k3_subset_1(X6,sK2(X5))) )
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(resolution,[],[f121,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
        | k1_xboole_0 = X0 )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( spl3_19
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f114,f111,f63,f120])).

fof(f63,plain,
    ( spl3_6
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK2(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f111,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
        | r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0))
        | k1_xboole_0 = X0 )
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(resolution,[],[f112,f64])).

fof(f64,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f112,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f113,plain,
    ( spl3_17
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f109,f106,f68,f111])).

fof(f68,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f106,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f107,f69])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f38,f106])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f104,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f37,f102])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

fof(f91,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f36,f89])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f87,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f35,f85])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f82,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f78,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f70,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f41,f68])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f65,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f61,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f40,f59])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f57,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

fof(f53,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f51])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f49,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f27,f43])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:53 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.45  % (12141)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (12149)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.47  % (12141)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f225,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f45,f49,f53,f57,f61,f65,f70,f78,f82,f87,f91,f104,f108,f113,f122,f141,f148,f161,f176,f199,f217,f224])).
% 0.20/0.47  fof(f224,plain,(
% 0.20/0.47    ~spl3_2 | ~spl3_12 | spl3_30),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f223])).
% 0.20/0.47  fof(f223,plain,(
% 0.20/0.47    $false | (~spl3_2 | ~spl3_12 | spl3_30)),
% 0.20/0.47    inference(subsumption_resolution,[],[f220,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f220,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_12 | spl3_30)),
% 0.20/0.47    inference(resolution,[],[f216,f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl3_12 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f215])).
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    spl3_30 <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    ~spl3_30 | ~spl3_10 | spl3_27),
% 0.20/0.47    inference(avatar_split_clause,[],[f204,f197,f80,f215])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl3_10 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    spl3_27 <=> m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_10 | spl3_27)),
% 0.20/0.47    inference(resolution,[],[f198,f81])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f80])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    ~m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | spl3_27),
% 0.20/0.47    inference(avatar_component_clause,[],[f197])).
% 0.20/0.47  fof(f199,plain,(
% 0.20/0.47    ~spl3_27 | spl3_4 | ~spl3_9 | ~spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f187,f156,f76,f55,f197])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl3_4 <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl3_9 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    spl3_23 <=> k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    ~m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | (spl3_4 | ~spl3_9 | ~spl3_23)),
% 0.20/0.47    inference(subsumption_resolution,[],[f186,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f55])).
% 0.20/0.47  % (12139)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | ~m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | (~spl3_9 | ~spl3_23)),
% 0.20/0.47    inference(superposition,[],[f77,f157])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | ~spl3_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f156])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f76])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_21 | ~spl3_24),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f175])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_21 | ~spl3_24)),
% 0.20/0.47    inference(subsumption_resolution,[],[f174,f48])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl3_1 | ~spl3_3 | ~spl3_21 | ~spl3_24)),
% 0.20/0.47    inference(subsumption_resolution,[],[f173,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    k1_xboole_0 != sK1 | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl3_1 <=> k1_xboole_0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_3 | ~spl3_21 | ~spl3_24)),
% 0.20/0.47    inference(subsumption_resolution,[],[f167,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl3_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2(sK1))) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_21 | ~spl3_24)),
% 0.20/0.47    inference(superposition,[],[f140,f160])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl3_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f159])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    spl3_24 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ( ! [X6,X5] : (~r1_tarski(k7_setfam_1(X6,X5),k3_subset_1(X6,sK2(X5))) | k1_xboole_0 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X6)))) ) | ~spl3_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f139])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    spl3_21 <=> ! [X5,X6] : (~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X6))) | k1_xboole_0 = X5 | ~r1_tarski(k7_setfam_1(X6,X5),k3_subset_1(X6,sK2(X5))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    spl3_23 | spl3_24 | ~spl3_2 | ~spl3_22),
% 0.20/0.47    inference(avatar_split_clause,[],[f154,f146,f47,f159,f156])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    spl3_22 <=> ! [X1,X0] : (k6_setfam_1(X0,X1) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1))) | k1_xboole_0 = k7_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    k1_xboole_0 = k7_setfam_1(sK0,sK1) | k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | (~spl3_2 | ~spl3_22)),
% 0.20/0.47    inference(resolution,[],[f147,f48])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = k7_setfam_1(X0,X1) | k6_setfam_1(X0,X1) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))) ) | ~spl3_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f146])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    spl3_22 | ~spl3_11 | ~spl3_12 | ~spl3_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f124,f102,f89,f85,f146])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl3_11 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    spl3_15 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1))) | k1_xboole_0 = k7_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl3_11 | ~spl3_12 | ~spl3_15)),
% 0.20/0.47    inference(subsumption_resolution,[],[f123,f90])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1))) | k1_xboole_0 = k7_setfam_1(X0,X1) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl3_11 | ~spl3_15)),
% 0.20/0.47    inference(superposition,[],[f103,f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f102])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    spl3_21 | ~spl3_5 | ~spl3_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f130,f120,f59,f139])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl3_5 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    spl3_19 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ( ! [X6,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X6))) | k1_xboole_0 = X5 | ~r1_tarski(k7_setfam_1(X6,X5),k3_subset_1(X6,sK2(X5)))) ) | (~spl3_5 | ~spl3_19)),
% 0.20/0.47    inference(resolution,[],[f121,f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | k1_xboole_0 = X0) ) | ~spl3_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f120])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    spl3_19 | ~spl3_6 | ~spl3_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f114,f111,f63,f120])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl3_6 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    spl3_17 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | r2_hidden(k3_subset_1(X1,sK2(X0)),k7_setfam_1(X1,X0)) | k1_xboole_0 = X0) ) | (~spl3_6 | ~spl3_17)),
% 0.20/0.47    inference(resolution,[],[f112,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) ) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f63])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) ) | ~spl3_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f111])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    spl3_17 | ~spl3_7 | ~spl3_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f109,f106,f68,f111])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl3_7 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl3_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) ) | (~spl3_7 | ~spl3_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f107,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) ) | ~spl3_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f106])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl3_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f106])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl3_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f102])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : (k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : ((k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f89])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f85])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f80])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl3_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f76])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f41,f68])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f63])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f59])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f28,f55])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0,X1] : ((k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f29,f51])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f47])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f43])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    k1_xboole_0 != sK1),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (12141)------------------------------
% 0.20/0.47  % (12141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (12141)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (12141)Memory used [KB]: 10746
% 0.20/0.47  % (12141)Time elapsed: 0.059 s
% 0.20/0.47  % (12141)------------------------------
% 0.20/0.47  % (12141)------------------------------
% 0.20/0.47  % (12131)Success in time 0.12 s
%------------------------------------------------------------------------------
