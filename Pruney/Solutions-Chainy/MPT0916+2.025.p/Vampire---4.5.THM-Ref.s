%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 345 expanded)
%              Number of leaves         :   45 ( 165 expanded)
%              Depth                    :    9
%              Number of atoms          :  593 (1367 expanded)
%              Number of equality atoms :   99 ( 168 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f291,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f68,f72,f82,f86,f92,f99,f106,f118,f138,f145,f149,f153,f159,f172,f178,f184,f190,f196,f202,f206,f224,f232,f240,f248,f262,f266,f275,f282,f285,f289])).

fof(f289,plain,
    ( ~ spl7_13
    | spl7_26
    | ~ spl7_36 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl7_13
    | spl7_26
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f287,f105])).

fof(f105,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_13
  <=> r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f287,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | spl7_26
    | ~ spl7_36 ),
    inference(forward_demodulation,[],[f171,f223])).

fof(f223,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl7_36
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f171,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl7_26
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f285,plain,
    ( ~ spl7_15
    | spl7_25
    | ~ spl7_39 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl7_15
    | spl7_25
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f283,f117])).

fof(f117,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl7_15
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f283,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | spl7_25
    | ~ spl7_39 ),
    inference(forward_demodulation,[],[f167,f274])).

fof(f274,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl7_39
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f167,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl7_25
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f282,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_24
    | spl7_33
    | spl7_34
    | spl7_35
    | ~ spl7_38 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_12
    | spl7_24
    | spl7_33
    | spl7_34
    | spl7_35
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f280,f98])).

fof(f98,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl7_12
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f280,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl7_6
    | spl7_24
    | spl7_33
    | spl7_34
    | spl7_35
    | ~ spl7_38 ),
    inference(backward_demodulation,[],[f163,f279])).

fof(f279,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl7_6
    | spl7_33
    | spl7_34
    | spl7_35
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f278,f210])).

fof(f210,plain,
    ( k1_xboole_0 != sK0
    | spl7_33 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl7_33
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f278,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | spl7_34
    | spl7_35
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f277,f214])).

% (7694)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f214,plain,
    ( k1_xboole_0 != sK1
    | spl7_34 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_34
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f277,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | spl7_35
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f276,f218])).

fof(f218,plain,
    ( k1_xboole_0 != sK2
    | spl7_35 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl7_35
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f276,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | ~ spl7_38 ),
    inference(resolution,[],[f265,f67])).

fof(f67,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl7_6
  <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f265,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl7_38
  <=> ! [X1,X3,X0,X2] :
        ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f163,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl7_24
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f275,plain,
    ( spl7_39
    | ~ spl7_6
    | spl7_33
    | spl7_34
    | spl7_35
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f270,f260,f217,f213,f209,f65,f272])).

fof(f260,plain,
    ( spl7_37
  <=> ! [X1,X3,X0,X2] :
        ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f270,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl7_6
    | spl7_33
    | spl7_34
    | spl7_35
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f269,f210])).

fof(f269,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | spl7_34
    | spl7_35
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f268,f214])).

fof(f268,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | spl7_35
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f267,f218])).

fof(f267,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | ~ spl7_37 ),
    inference(resolution,[],[f261,f67])).

fof(f261,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f260])).

fof(f266,plain,(
    spl7_38 ),
    inference(avatar_split_clause,[],[f39,f264])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f262,plain,(
    spl7_37 ),
    inference(avatar_split_clause,[],[f38,f260])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f29])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f248,plain,
    ( ~ spl7_1
    | spl7_31
    | ~ spl7_35 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl7_1
    | spl7_31
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f246,f42])).

fof(f42,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl7_1
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f246,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_mcart_1(sK6))
    | spl7_31
    | ~ spl7_35 ),
    inference(backward_demodulation,[],[f201,f219])).

fof(f219,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f217])).

fof(f201,plain,
    ( ~ r1_tarski(sK2,k2_mcart_1(sK6))
    | spl7_31 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl7_31
  <=> r1_tarski(sK2,k2_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f240,plain,
    ( ~ spl7_1
    | spl7_29
    | ~ spl7_34 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl7_1
    | spl7_29
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f238,f42])).

fof(f238,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_mcart_1(k1_mcart_1(sK6)))
    | spl7_29
    | ~ spl7_34 ),
    inference(backward_demodulation,[],[f189,f215])).

fof(f215,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f213])).

fof(f189,plain,
    ( ~ r1_tarski(sK1,k2_mcart_1(k1_mcart_1(sK6)))
    | spl7_29 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl7_29
  <=> r1_tarski(sK1,k2_mcart_1(k1_mcart_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f232,plain,
    ( ~ spl7_1
    | spl7_27
    | ~ spl7_33 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl7_1
    | spl7_27
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f230,f42])).

fof(f230,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_mcart_1(k1_mcart_1(sK6)))
    | spl7_27
    | ~ spl7_33 ),
    inference(backward_demodulation,[],[f177,f211])).

fof(f211,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f209])).

fof(f177,plain,
    ( ~ r1_tarski(sK0,k1_mcart_1(k1_mcart_1(sK6)))
    | spl7_27 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl7_27
  <=> r1_tarski(sK0,k1_mcart_1(k1_mcart_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f224,plain,
    ( spl7_33
    | spl7_34
    | spl7_35
    | spl7_36
    | ~ spl7_6
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f207,f204,f65,f221,f217,f213,f209])).

fof(f204,plain,
    ( spl7_32
  <=> ! [X1,X3,X0,X2] :
        ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f207,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_6
    | ~ spl7_32 ),
    inference(resolution,[],[f205,f67])).

fof(f205,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,(
    spl7_32 ),
    inference(avatar_split_clause,[],[f37,f204])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f29])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f202,plain,
    ( ~ spl7_31
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f197,f193,f70,f199])).

fof(f70,plain,
    ( spl7_7
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,X0)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f193,plain,
    ( spl7_30
  <=> r2_hidden(k2_mcart_1(sK6),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f197,plain,
    ( ~ r1_tarski(sK2,k2_mcart_1(sK6))
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(resolution,[],[f195,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f195,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK2)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f193])).

fof(f196,plain,
    ( spl7_30
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f191,f151,f103,f193])).

fof(f151,plain,
    ( spl7_22
  <=> ! [X2] :
        ( ~ r2_hidden(X2,sK5)
        | r2_hidden(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f191,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK2)
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(resolution,[],[f152,f105])).

fof(f152,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK5)
        | r2_hidden(X2,sK2) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f151])).

fof(f190,plain,
    ( ~ spl7_29
    | ~ spl7_7
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f185,f181,f70,f187])).

fof(f181,plain,
    ( spl7_28
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f185,plain,
    ( ~ r1_tarski(sK1,k2_mcart_1(k1_mcart_1(sK6)))
    | ~ spl7_7
    | ~ spl7_28 ),
    inference(resolution,[],[f183,f71])).

fof(f183,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK1)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f181])).

fof(f184,plain,
    ( spl7_28
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f179,f147,f115,f181])).

fof(f147,plain,
    ( spl7_21
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK4)
        | r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f179,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK1)
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(resolution,[],[f148,f117])).

fof(f148,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK4)
        | r2_hidden(X1,sK1) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f147])).

fof(f178,plain,
    ( ~ spl7_27
    | ~ spl7_7
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f173,f156,f70,f175])).

fof(f156,plain,
    ( spl7_23
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f173,plain,
    ( ~ r1_tarski(sK0,k1_mcart_1(k1_mcart_1(sK6)))
    | ~ spl7_7
    | ~ spl7_23 ),
    inference(resolution,[],[f158,f71])).

fof(f158,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK0)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f156])).

fof(f172,plain,
    ( ~ spl7_24
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f25,f169,f165,f161])).

fof(f25,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
    & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f18,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                  & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                  | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
            & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
                | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
              & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
              | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
              | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
            & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
            & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
   => ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
            | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
            | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
          & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
          & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X6] :
        ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
          | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
          | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
        & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
        & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
        | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
        | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
      & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
      & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f159,plain,
    ( spl7_23
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f154,f143,f96,f156])).

fof(f143,plain,
    ( spl7_20
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f154,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK0)
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(resolution,[],[f144,f98])).

% (7683)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f144,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,sK0) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f143])).

fof(f153,plain,
    ( spl7_22
    | ~ spl7_4
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f141,f136,f55,f151])).

fof(f55,plain,
    ( spl7_4
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f136,plain,
    ( spl7_19
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f141,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK5)
        | r2_hidden(X2,sK2) )
    | ~ spl7_4
    | ~ spl7_19 ),
    inference(resolution,[],[f137,f57])).

fof(f57,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(X2,X0) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f136])).

fof(f149,plain,
    ( spl7_21
    | ~ spl7_3
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f140,f136,f50,f147])).

fof(f50,plain,
    ( spl7_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f140,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK4)
        | r2_hidden(X1,sK1) )
    | ~ spl7_3
    | ~ spl7_19 ),
    inference(resolution,[],[f137,f52])).

fof(f52,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f145,plain,
    ( spl7_20
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f139,f136,f45,f143])).

fof(f45,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,sK0) )
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(resolution,[],[f137,f47])).

fof(f47,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f138,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f27,f136])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f118,plain,
    ( spl7_15
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f101,f89,f84,f115])).

fof(f84,plain,
    ( spl7_10
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k2_mcart_1(X0),X2)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f89,plain,
    ( spl7_11
  <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f101,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(resolution,[],[f85,f91])).

fof(f91,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f85,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | r2_hidden(k2_mcart_1(X0),X2) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f106,plain,
    ( spl7_13
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f100,f84,f60,f103])).

fof(f60,plain,
    ( spl7_5
  <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f100,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(resolution,[],[f85,f62])).

fof(f62,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f99,plain,
    ( spl7_12
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f93,f89,f80,f96])).

% (7684)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f80,plain,
    ( spl7_9
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k1_mcart_1(X0),X1)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f93,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(resolution,[],[f91,f81])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | r2_hidden(k1_mcart_1(X0),X1) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f92,plain,
    ( spl7_11
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f87,f80,f60,f89])).

fof(f87,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(resolution,[],[f81,f62])).

fof(f86,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f31,f84])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f82,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f30,f80])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f68,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f23,f29])).

fof(f23,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f35,f60])).

fof(f35,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f24,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f26,f41])).

% (7690)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% (7679)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (7682)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (7686)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (7681)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (7686)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f291,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f68,f72,f82,f86,f92,f99,f106,f118,f138,f145,f149,f153,f159,f172,f178,f184,f190,f196,f202,f206,f224,f232,f240,f248,f262,f266,f275,f282,f285,f289])).
% 0.20/0.46  fof(f289,plain,(
% 0.20/0.46    ~spl7_13 | spl7_26 | ~spl7_36),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f288])).
% 0.20/0.46  fof(f288,plain,(
% 0.20/0.46    $false | (~spl7_13 | spl7_26 | ~spl7_36)),
% 0.20/0.46    inference(subsumption_resolution,[],[f287,f105])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl7_13),
% 0.20/0.46    inference(avatar_component_clause,[],[f103])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    spl7_13 <=> r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.46  fof(f287,plain,(
% 0.20/0.46    ~r2_hidden(k2_mcart_1(sK6),sK5) | (spl7_26 | ~spl7_36)),
% 0.20/0.46    inference(forward_demodulation,[],[f171,f223])).
% 0.20/0.46  fof(f223,plain,(
% 0.20/0.46    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | ~spl7_36),
% 0.20/0.46    inference(avatar_component_clause,[],[f221])).
% 0.20/0.46  fof(f221,plain,(
% 0.20/0.46    spl7_36 <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.20/0.46  fof(f171,plain,(
% 0.20/0.46    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl7_26),
% 0.20/0.46    inference(avatar_component_clause,[],[f169])).
% 0.20/0.46  fof(f169,plain,(
% 0.20/0.46    spl7_26 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.20/0.46  fof(f285,plain,(
% 0.20/0.46    ~spl7_15 | spl7_25 | ~spl7_39),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f284])).
% 0.20/0.46  fof(f284,plain,(
% 0.20/0.46    $false | (~spl7_15 | spl7_25 | ~spl7_39)),
% 0.20/0.46    inference(subsumption_resolution,[],[f283,f117])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl7_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f115])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    spl7_15 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.46  fof(f283,plain,(
% 0.20/0.46    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | (spl7_25 | ~spl7_39)),
% 0.20/0.46    inference(forward_demodulation,[],[f167,f274])).
% 0.20/0.46  fof(f274,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | ~spl7_39),
% 0.20/0.46    inference(avatar_component_clause,[],[f272])).
% 0.20/0.46  fof(f272,plain,(
% 0.20/0.46    spl7_39 <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.20/0.46  fof(f167,plain,(
% 0.20/0.46    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl7_25),
% 0.20/0.46    inference(avatar_component_clause,[],[f165])).
% 0.20/0.46  fof(f165,plain,(
% 0.20/0.46    spl7_25 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.20/0.46  fof(f282,plain,(
% 0.20/0.46    ~spl7_6 | ~spl7_12 | spl7_24 | spl7_33 | spl7_34 | spl7_35 | ~spl7_38),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f281])).
% 0.20/0.46  fof(f281,plain,(
% 0.20/0.46    $false | (~spl7_6 | ~spl7_12 | spl7_24 | spl7_33 | spl7_34 | spl7_35 | ~spl7_38)),
% 0.20/0.46    inference(subsumption_resolution,[],[f280,f98])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl7_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f96])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    spl7_12 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.46  fof(f280,plain,(
% 0.20/0.46    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | (~spl7_6 | spl7_24 | spl7_33 | spl7_34 | spl7_35 | ~spl7_38)),
% 0.20/0.46    inference(backward_demodulation,[],[f163,f279])).
% 0.20/0.46  fof(f279,plain,(
% 0.20/0.46    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | (~spl7_6 | spl7_33 | spl7_34 | spl7_35 | ~spl7_38)),
% 0.20/0.46    inference(subsumption_resolution,[],[f278,f210])).
% 0.20/0.46  fof(f210,plain,(
% 0.20/0.46    k1_xboole_0 != sK0 | spl7_33),
% 0.20/0.46    inference(avatar_component_clause,[],[f209])).
% 0.20/0.46  fof(f209,plain,(
% 0.20/0.46    spl7_33 <=> k1_xboole_0 = sK0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.20/0.46  fof(f278,plain,(
% 0.20/0.46    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK0 | (~spl7_6 | spl7_34 | spl7_35 | ~spl7_38)),
% 0.20/0.46    inference(subsumption_resolution,[],[f277,f214])).
% 0.20/0.46  % (7694)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  fof(f214,plain,(
% 0.20/0.46    k1_xboole_0 != sK1 | spl7_34),
% 0.20/0.46    inference(avatar_component_clause,[],[f213])).
% 0.20/0.46  fof(f213,plain,(
% 0.20/0.46    spl7_34 <=> k1_xboole_0 = sK1),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.20/0.46  fof(f277,plain,(
% 0.20/0.46    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_6 | spl7_35 | ~spl7_38)),
% 0.20/0.46    inference(subsumption_resolution,[],[f276,f218])).
% 0.20/0.46  fof(f218,plain,(
% 0.20/0.46    k1_xboole_0 != sK2 | spl7_35),
% 0.20/0.46    inference(avatar_component_clause,[],[f217])).
% 0.20/0.46  fof(f217,plain,(
% 0.20/0.46    spl7_35 <=> k1_xboole_0 = sK2),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.20/0.46  fof(f276,plain,(
% 0.20/0.46    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_6 | ~spl7_38)),
% 0.20/0.46    inference(resolution,[],[f265,f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl7_6 <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.46  fof(f265,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl7_38),
% 0.20/0.46    inference(avatar_component_clause,[],[f264])).
% 0.20/0.46  fof(f264,plain,(
% 0.20/0.46    spl7_38 <=> ! [X1,X3,X0,X2] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.20/0.46  fof(f163,plain,(
% 0.20/0.46    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl7_24),
% 0.20/0.46    inference(avatar_component_clause,[],[f161])).
% 0.20/0.46  fof(f161,plain,(
% 0.20/0.46    spl7_24 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.20/0.46  fof(f275,plain,(
% 0.20/0.46    spl7_39 | ~spl7_6 | spl7_33 | spl7_34 | spl7_35 | ~spl7_37),
% 0.20/0.46    inference(avatar_split_clause,[],[f270,f260,f217,f213,f209,f65,f272])).
% 0.20/0.46  fof(f260,plain,(
% 0.20/0.46    spl7_37 <=> ! [X1,X3,X0,X2] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.20/0.46  fof(f270,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | (~spl7_6 | spl7_33 | spl7_34 | spl7_35 | ~spl7_37)),
% 0.20/0.46    inference(subsumption_resolution,[],[f269,f210])).
% 0.20/0.46  fof(f269,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK0 | (~spl7_6 | spl7_34 | spl7_35 | ~spl7_37)),
% 0.20/0.46    inference(subsumption_resolution,[],[f268,f214])).
% 0.20/0.46  fof(f268,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_6 | spl7_35 | ~spl7_37)),
% 0.20/0.46    inference(subsumption_resolution,[],[f267,f218])).
% 0.20/0.46  fof(f267,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_6 | ~spl7_37)),
% 0.20/0.46    inference(resolution,[],[f261,f67])).
% 0.20/0.46  fof(f261,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl7_37),
% 0.20/0.46    inference(avatar_component_clause,[],[f260])).
% 0.20/0.46  fof(f266,plain,(
% 0.20/0.46    spl7_38),
% 0.20/0.46    inference(avatar_split_clause,[],[f39,f264])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(definition_unfolding,[],[f32,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.46  fof(f262,plain,(
% 0.20/0.46    spl7_37),
% 0.20/0.46    inference(avatar_split_clause,[],[f38,f260])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(definition_unfolding,[],[f33,f29])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f248,plain,(
% 0.20/0.46    ~spl7_1 | spl7_31 | ~spl7_35),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f247])).
% 0.20/0.46  fof(f247,plain,(
% 0.20/0.46    $false | (~spl7_1 | spl7_31 | ~spl7_35)),
% 0.20/0.46    inference(subsumption_resolution,[],[f246,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl7_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    spl7_1 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.46  fof(f246,plain,(
% 0.20/0.46    ~r1_tarski(k1_xboole_0,k2_mcart_1(sK6)) | (spl7_31 | ~spl7_35)),
% 0.20/0.46    inference(backward_demodulation,[],[f201,f219])).
% 0.20/0.46  fof(f219,plain,(
% 0.20/0.46    k1_xboole_0 = sK2 | ~spl7_35),
% 0.20/0.46    inference(avatar_component_clause,[],[f217])).
% 0.20/0.46  fof(f201,plain,(
% 0.20/0.46    ~r1_tarski(sK2,k2_mcart_1(sK6)) | spl7_31),
% 0.20/0.46    inference(avatar_component_clause,[],[f199])).
% 0.20/0.46  fof(f199,plain,(
% 0.20/0.46    spl7_31 <=> r1_tarski(sK2,k2_mcart_1(sK6))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.20/0.46  fof(f240,plain,(
% 0.20/0.46    ~spl7_1 | spl7_29 | ~spl7_34),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f239])).
% 0.20/0.46  fof(f239,plain,(
% 0.20/0.46    $false | (~spl7_1 | spl7_29 | ~spl7_34)),
% 0.20/0.46    inference(subsumption_resolution,[],[f238,f42])).
% 0.20/0.46  fof(f238,plain,(
% 0.20/0.46    ~r1_tarski(k1_xboole_0,k2_mcart_1(k1_mcart_1(sK6))) | (spl7_29 | ~spl7_34)),
% 0.20/0.46    inference(backward_demodulation,[],[f189,f215])).
% 0.20/0.46  fof(f215,plain,(
% 0.20/0.46    k1_xboole_0 = sK1 | ~spl7_34),
% 0.20/0.46    inference(avatar_component_clause,[],[f213])).
% 0.20/0.46  fof(f189,plain,(
% 0.20/0.46    ~r1_tarski(sK1,k2_mcart_1(k1_mcart_1(sK6))) | spl7_29),
% 0.20/0.46    inference(avatar_component_clause,[],[f187])).
% 0.20/0.46  fof(f187,plain,(
% 0.20/0.46    spl7_29 <=> r1_tarski(sK1,k2_mcart_1(k1_mcart_1(sK6)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.20/0.46  fof(f232,plain,(
% 0.20/0.46    ~spl7_1 | spl7_27 | ~spl7_33),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f231])).
% 0.20/0.46  fof(f231,plain,(
% 0.20/0.46    $false | (~spl7_1 | spl7_27 | ~spl7_33)),
% 0.20/0.46    inference(subsumption_resolution,[],[f230,f42])).
% 0.20/0.46  fof(f230,plain,(
% 0.20/0.46    ~r1_tarski(k1_xboole_0,k1_mcart_1(k1_mcart_1(sK6))) | (spl7_27 | ~spl7_33)),
% 0.20/0.46    inference(backward_demodulation,[],[f177,f211])).
% 0.20/0.46  fof(f211,plain,(
% 0.20/0.46    k1_xboole_0 = sK0 | ~spl7_33),
% 0.20/0.46    inference(avatar_component_clause,[],[f209])).
% 0.20/0.46  fof(f177,plain,(
% 0.20/0.46    ~r1_tarski(sK0,k1_mcart_1(k1_mcart_1(sK6))) | spl7_27),
% 0.20/0.46    inference(avatar_component_clause,[],[f175])).
% 0.20/0.46  fof(f175,plain,(
% 0.20/0.46    spl7_27 <=> r1_tarski(sK0,k1_mcart_1(k1_mcart_1(sK6)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.20/0.46  fof(f224,plain,(
% 0.20/0.46    spl7_33 | spl7_34 | spl7_35 | spl7_36 | ~spl7_6 | ~spl7_32),
% 0.20/0.46    inference(avatar_split_clause,[],[f207,f204,f65,f221,f217,f213,f209])).
% 0.20/0.46  fof(f204,plain,(
% 0.20/0.46    spl7_32 <=> ! [X1,X3,X0,X2] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.20/0.46  fof(f207,plain,(
% 0.20/0.46    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_6 | ~spl7_32)),
% 0.20/0.46    inference(resolution,[],[f205,f67])).
% 0.20/0.46  fof(f205,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl7_32),
% 0.20/0.46    inference(avatar_component_clause,[],[f204])).
% 0.20/0.46  fof(f206,plain,(
% 0.20/0.46    spl7_32),
% 0.20/0.46    inference(avatar_split_clause,[],[f37,f204])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(definition_unfolding,[],[f34,f29])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f202,plain,(
% 0.20/0.46    ~spl7_31 | ~spl7_7 | ~spl7_30),
% 0.20/0.46    inference(avatar_split_clause,[],[f197,f193,f70,f199])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    spl7_7 <=> ! [X1,X0] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.46  fof(f193,plain,(
% 0.20/0.46    spl7_30 <=> r2_hidden(k2_mcart_1(sK6),sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.20/0.46  fof(f197,plain,(
% 0.20/0.46    ~r1_tarski(sK2,k2_mcart_1(sK6)) | (~spl7_7 | ~spl7_30)),
% 0.20/0.46    inference(resolution,[],[f195,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl7_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f70])).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(sK6),sK2) | ~spl7_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f193])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    spl7_30 | ~spl7_13 | ~spl7_22),
% 0.20/0.47    inference(avatar_split_clause,[],[f191,f151,f103,f193])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    spl7_22 <=> ! [X2] : (~r2_hidden(X2,sK5) | r2_hidden(X2,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(sK6),sK2) | (~spl7_13 | ~spl7_22)),
% 0.20/0.47    inference(resolution,[],[f152,f105])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    ( ! [X2] : (~r2_hidden(X2,sK5) | r2_hidden(X2,sK2)) ) | ~spl7_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f151])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    ~spl7_29 | ~spl7_7 | ~spl7_28),
% 0.20/0.47    inference(avatar_split_clause,[],[f185,f181,f70,f187])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    spl7_28 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    ~r1_tarski(sK1,k2_mcart_1(k1_mcart_1(sK6))) | (~spl7_7 | ~spl7_28)),
% 0.20/0.47    inference(resolution,[],[f183,f71])).
% 0.20/0.47  fof(f183,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK1) | ~spl7_28),
% 0.20/0.47    inference(avatar_component_clause,[],[f181])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    spl7_28 | ~spl7_15 | ~spl7_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f179,f147,f115,f181])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    spl7_21 <=> ! [X1] : (~r2_hidden(X1,sK4) | r2_hidden(X1,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK1) | (~spl7_15 | ~spl7_21)),
% 0.20/0.47    inference(resolution,[],[f148,f117])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    ( ! [X1] : (~r2_hidden(X1,sK4) | r2_hidden(X1,sK1)) ) | ~spl7_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f147])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ~spl7_27 | ~spl7_7 | ~spl7_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f173,f156,f70,f175])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    spl7_23 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    ~r1_tarski(sK0,k1_mcart_1(k1_mcart_1(sK6))) | (~spl7_7 | ~spl7_23)),
% 0.20/0.47    inference(resolution,[],[f158,f71])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK0) | ~spl7_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f156])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    ~spl7_24 | ~spl7_25 | ~spl7_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f169,f165,f161])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ((((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f18,f17,f16,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) => ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    spl7_23 | ~spl7_12 | ~spl7_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f154,f143,f96,f156])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    spl7_20 <=> ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK0) | (~spl7_12 | ~spl7_20)),
% 0.20/0.47    inference(resolution,[],[f144,f98])).
% 0.20/0.47  % (7683)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK0)) ) | ~spl7_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f143])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    spl7_22 | ~spl7_4 | ~spl7_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f141,f136,f55,f151])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl7_4 <=> m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    spl7_19 <=> ! [X1,X0,X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ( ! [X2] : (~r2_hidden(X2,sK5) | r2_hidden(X2,sK2)) ) | (~spl7_4 | ~spl7_19)),
% 0.20/0.47    inference(resolution,[],[f137,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    m1_subset_1(sK5,k1_zfmisc_1(sK2)) | ~spl7_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f55])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) ) | ~spl7_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f136])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    spl7_21 | ~spl7_3 | ~spl7_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f140,f136,f50,f147])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl7_3 <=> m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ( ! [X1] : (~r2_hidden(X1,sK4) | r2_hidden(X1,sK1)) ) | (~spl7_3 | ~spl7_19)),
% 0.20/0.47    inference(resolution,[],[f137,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    m1_subset_1(sK4,k1_zfmisc_1(sK1)) | ~spl7_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f50])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    spl7_20 | ~spl7_2 | ~spl7_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f139,f136,f45,f143])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK0)) ) | (~spl7_2 | ~spl7_19)),
% 0.20/0.47    inference(resolution,[],[f137,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl7_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f45])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    spl7_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f136])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl7_15 | ~spl7_10 | ~spl7_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f101,f89,f84,f115])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl7_10 <=> ! [X1,X0,X2] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl7_11 <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | (~spl7_10 | ~spl7_11)),
% 0.20/0.47    inference(resolution,[],[f85,f91])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl7_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f89])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) ) | ~spl7_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f84])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl7_13 | ~spl7_5 | ~spl7_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f100,f84,f60,f103])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    spl7_5 <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(sK6),sK5) | (~spl7_5 | ~spl7_10)),
% 0.20/0.47    inference(resolution,[],[f85,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl7_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f60])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl7_12 | ~spl7_9 | ~spl7_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f93,f89,f80,f96])).
% 0.20/0.47  % (7684)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl7_9 <=> ! [X1,X0,X2] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | (~spl7_9 | ~spl7_11)),
% 0.20/0.47    inference(resolution,[],[f91,f81])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) ) | ~spl7_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f80])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    spl7_11 | ~spl7_5 | ~spl7_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f87,f80,f60,f89])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | (~spl7_5 | ~spl7_9)),
% 0.20/0.47    inference(resolution,[],[f81,f62])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl7_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f84])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl7_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f80])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    spl7_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f28,f70])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl7_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f65])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.47    inference(definition_unfolding,[],[f23,f29])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl7_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f60])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.47    inference(definition_unfolding,[],[f24,f29])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl7_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f55])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f50])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl7_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f45])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl7_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f41])).
% 0.20/0.47  % (7690)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (7679)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (7686)------------------------------
% 0.20/0.48  % (7686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (7686)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (7686)Memory used [KB]: 6268
% 0.20/0.48  % (7686)Time elapsed: 0.066 s
% 0.20/0.48  % (7686)------------------------------
% 0.20/0.48  % (7686)------------------------------
% 0.20/0.48  % (7692)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (7685)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (7678)Success in time 0.119 s
%------------------------------------------------------------------------------
