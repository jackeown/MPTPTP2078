%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 203 expanded)
%              Number of leaves         :   23 (  80 expanded)
%              Depth                    :    7
%              Number of atoms          :  272 ( 538 expanded)
%              Number of equality atoms :   42 ( 134 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f261,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f48,f53,f67,f73,f95,f101,f108,f114,f123,f143,f151,f167,f172,f196,f221,f253,f260])).

fof(f260,plain,
    ( spl7_1
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl7_1
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f33,f254,f17])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f254,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK0)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f147,f46])).

fof(f46,plain,
    ( sK0 = sK2
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl7_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f147,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK2)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_17
  <=> ! [X7] : ~ r2_hidden(X7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f33,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

% (3965)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f253,plain,
    ( spl7_19
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f252,f149,f164])).

fof(f164,plain,
    ( spl7_19
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f149,plain,
    ( spl7_18
  <=> ! [X6] :
        ( ~ r2_hidden(X6,sK3)
        | r2_hidden(X6,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f252,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl7_18 ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
    ( r1_tarski(sK3,sK1)
    | r1_tarski(sK3,sK1)
    | ~ spl7_18 ),
    inference(resolution,[],[f160,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f160,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,sK1),sK3)
        | r1_tarski(X1,sK1) )
    | ~ spl7_18 ),
    inference(resolution,[],[f150,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f150,plain,
    ( ! [X6] :
        ( r2_hidden(X6,sK1)
        | ~ r2_hidden(X6,sK3) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f221,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f38,f214,f17])).

fof(f214,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK1)
    | ~ spl7_3
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f122,f42])).

fof(f42,plain,
    ( sK1 = sK3
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl7_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f122,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK3)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl7_14
  <=> ! [X4] : ~ r2_hidden(X4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f38,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f196,plain,
    ( ~ spl7_14
    | spl7_19 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl7_14
    | spl7_19 ),
    inference(unit_resulting_resolution,[],[f166,f122,f19])).

fof(f166,plain,
    ( ~ r1_tarski(sK3,sK1)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f164])).

fof(f172,plain,
    ( spl7_10
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f171,f118,f98])).

fof(f98,plain,
    ( spl7_10
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f118,plain,
    ( spl7_13
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f171,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl7_13 ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,
    ( r1_tarski(sK2,sK0)
    | r1_tarski(sK2,sK0)
    | ~ spl7_13 ),
    inference(resolution,[],[f125,f19])).

fof(f125,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,sK0),sK2)
        | r1_tarski(X1,sK0) )
    | ~ spl7_13 ),
    inference(resolution,[],[f119,f20])).

fof(f119,plain,
    ( ! [X5] :
        ( r2_hidden(X5,sK0)
        | ~ r2_hidden(X5,sK2) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f167,plain,
    ( ~ spl7_19
    | spl7_3
    | spl7_16 ),
    inference(avatar_split_clause,[],[f144,f140,f41,f164])).

fof(f140,plain,
    ( spl7_16
  <=> r2_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f144,plain,
    ( sK1 = sK3
    | ~ r1_tarski(sK3,sK1)
    | spl7_16 ),
    inference(resolution,[],[f142,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f142,plain,
    ( ~ r2_xboole_0(sK3,sK1)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f151,plain,
    ( spl7_17
    | spl7_18
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f90,f50,f149,f146])).

fof(f50,plain,
    ( spl7_5
  <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f90,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X7,sK2)
        | r2_hidden(X6,sK1) )
    | ~ spl7_5 ),
    inference(resolution,[],[f56,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f56,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X5,sK3)
        | ~ r2_hidden(X4,sK2) )
    | ~ spl7_5 ),
    inference(superposition,[],[f28,f52])).

fof(f52,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f143,plain,
    ( ~ spl7_16
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f138,f106,f140])).

fof(f106,plain,
    ( spl7_12
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f138,plain,
    ( ~ r2_xboole_0(sK3,sK1)
    | ~ spl7_12 ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
    ( ~ r2_xboole_0(sK3,sK1)
    | ~ r2_xboole_0(sK3,sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f116,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f116,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK6(sK3,X1),sK1)
        | ~ r2_xboole_0(sK3,X1) )
    | ~ spl7_12 ),
    inference(resolution,[],[f107,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f107,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f123,plain,
    ( spl7_13
    | spl7_14
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f89,f50,f121,f118])).

fof(f89,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK3)
        | ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f56,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f114,plain,
    ( spl7_1
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl7_1
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f33,f104,f17])).

fof(f104,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_11
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f108,plain,
    ( spl7_11
    | spl7_12
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f59,f50,f106,f103])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f55,f28])).

fof(f55,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK3) )
    | ~ spl7_5 ),
    inference(superposition,[],[f27,f52])).

fof(f101,plain,
    ( ~ spl7_10
    | spl7_4
    | spl7_9 ),
    inference(avatar_split_clause,[],[f96,f92,f45,f98])).

fof(f92,plain,
    ( spl7_9
  <=> r2_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f96,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK2,sK0)
    | spl7_9 ),
    inference(resolution,[],[f94,f23])).

fof(f94,plain,
    ( ~ r2_xboole_0(sK2,sK0)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f95,plain,
    ( ~ spl7_9
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f86,f65,f92])).

fof(f65,plain,
    ( spl7_7
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f86,plain,
    ( ~ r2_xboole_0(sK2,sK0)
    | ~ spl7_7 ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( ~ r2_xboole_0(sK2,sK0)
    | ~ r2_xboole_0(sK2,sK0)
    | ~ spl7_7 ),
    inference(resolution,[],[f75,f24])).

fof(f75,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK6(sK2,X1),sK0)
        | ~ r2_xboole_0(sK2,X1) )
    | ~ spl7_7 ),
    inference(resolution,[],[f66,f25])).

fof(f66,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f73,plain,
    ( spl7_2
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl7_2
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f38,f63,f17])).

fof(f63,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f62])).

% (3948)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f62,plain,
    ( spl7_6
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f67,plain,
    ( spl7_6
    | spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f57,f50,f65,f62])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f54,f28])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK2) )
    | ~ spl7_5 ),
    inference(superposition,[],[f26,f52])).

fof(f53,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f14,f50])).

fof(f14,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f48,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f13,f45,f41])).

fof(f13,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:11:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (3950)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (3967)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (3974)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (3959)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (3951)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (3958)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (3955)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (3957)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (3967)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f34,f39,f48,f53,f67,f73,f95,f101,f108,f114,f123,f143,f151,f167,f172,f196,f221,f253,f260])).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    spl7_1 | ~spl7_4 | ~spl7_17),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f255])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    $false | (spl7_1 | ~spl7_4 | ~spl7_17)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f33,f254,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    ( ! [X7] : (~r2_hidden(X7,sK0)) ) | (~spl7_4 | ~spl7_17)),
% 0.21/0.53    inference(forward_demodulation,[],[f147,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    sK0 = sK2 | ~spl7_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    spl7_4 <=> sK0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ( ! [X7] : (~r2_hidden(X7,sK2)) ) | ~spl7_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f146])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    spl7_17 <=> ! [X7] : ~r2_hidden(X7,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    k1_xboole_0 != sK0 | spl7_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    spl7_1 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  % (3965)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    spl7_19 | ~spl7_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f252,f149,f164])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    spl7_19 <=> r1_tarski(sK3,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    spl7_18 <=> ! [X6] : (~r2_hidden(X6,sK3) | r2_hidden(X6,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    r1_tarski(sK3,sK1) | ~spl7_18),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f250])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    r1_tarski(sK3,sK1) | r1_tarski(sK3,sK1) | ~spl7_18),
% 0.21/0.53    inference(resolution,[],[f160,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK5(X1,sK1),sK3) | r1_tarski(X1,sK1)) ) | ~spl7_18),
% 0.21/0.53    inference(resolution,[],[f150,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    ( ! [X6] : (r2_hidden(X6,sK1) | ~r2_hidden(X6,sK3)) ) | ~spl7_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f149])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    spl7_2 | ~spl7_3 | ~spl7_14),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f216])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    $false | (spl7_2 | ~spl7_3 | ~spl7_14)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f38,f214,f17])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,sK1)) ) | (~spl7_3 | ~spl7_14)),
% 0.21/0.53    inference(forward_demodulation,[],[f122,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    sK1 = sK3 | ~spl7_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    spl7_3 <=> sK1 = sK3),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,sK3)) ) | ~spl7_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f121])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl7_14 <=> ! [X4] : ~r2_hidden(X4,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | spl7_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    ~spl7_14 | spl7_19),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    $false | (~spl7_14 | spl7_19)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f166,f122,f19])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ~r1_tarski(sK3,sK1) | spl7_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f164])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    spl7_10 | ~spl7_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f171,f118,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    spl7_10 <=> r1_tarski(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    spl7_13 <=> ! [X5] : (~r2_hidden(X5,sK2) | r2_hidden(X5,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    r1_tarski(sK2,sK0) | ~spl7_13),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f169])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    r1_tarski(sK2,sK0) | r1_tarski(sK2,sK0) | ~spl7_13),
% 0.21/0.53    inference(resolution,[],[f125,f19])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK5(X1,sK0),sK2) | r1_tarski(X1,sK0)) ) | ~spl7_13),
% 0.21/0.53    inference(resolution,[],[f119,f20])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X5] : (r2_hidden(X5,sK0) | ~r2_hidden(X5,sK2)) ) | ~spl7_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f118])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    ~spl7_19 | spl7_3 | spl7_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f144,f140,f41,f164])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    spl7_16 <=> r2_xboole_0(sK3,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    sK1 = sK3 | ~r1_tarski(sK3,sK1) | spl7_16),
% 0.21/0.53    inference(resolution,[],[f142,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    ~r2_xboole_0(sK3,sK1) | spl7_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f140])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    spl7_17 | spl7_18 | ~spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f90,f50,f149,f146])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    spl7_5 <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~r2_hidden(X6,sK3) | ~r2_hidden(X7,sK2) | r2_hidden(X6,sK1)) ) | ~spl7_5),
% 0.21/0.53    inference(resolution,[],[f56,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) ) | ~spl7_5),
% 0.21/0.53    inference(superposition,[],[f28,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) | ~spl7_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f50])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    ~spl7_16 | ~spl7_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f138,f106,f140])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl7_12 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ~r2_xboole_0(sK3,sK1) | ~spl7_12),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    ~r2_xboole_0(sK3,sK1) | ~r2_xboole_0(sK3,sK1) | ~spl7_12),
% 0.21/0.53    inference(resolution,[],[f116,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK6(sK3,X1),sK1) | ~r2_xboole_0(sK3,X1)) ) | ~spl7_12),
% 0.21/0.53    inference(resolution,[],[f107,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl7_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f106])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    spl7_13 | spl7_14 | ~spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f89,f50,f121,f118])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~r2_hidden(X4,sK3) | ~r2_hidden(X5,sK2) | r2_hidden(X5,sK0)) ) | ~spl7_5),
% 0.21/0.53    inference(resolution,[],[f56,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl7_1 | ~spl7_11),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    $false | (spl7_1 | ~spl7_11)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f33,f104,f17])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl7_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    spl7_11 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    spl7_11 | spl7_12 | ~spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f59,f50,f106,f103])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl7_5),
% 0.21/0.53    inference(resolution,[],[f55,f28])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK3)) ) | ~spl7_5),
% 0.21/0.53    inference(superposition,[],[f27,f52])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ~spl7_10 | spl7_4 | spl7_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f96,f92,f45,f98])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl7_9 <=> r2_xboole_0(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    sK0 = sK2 | ~r1_tarski(sK2,sK0) | spl7_9),
% 0.21/0.53    inference(resolution,[],[f94,f23])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ~r2_xboole_0(sK2,sK0) | spl7_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f92])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ~spl7_9 | ~spl7_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f86,f65,f92])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl7_7 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ~r2_xboole_0(sK2,sK0) | ~spl7_7),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ~r2_xboole_0(sK2,sK0) | ~r2_xboole_0(sK2,sK0) | ~spl7_7),
% 0.21/0.53    inference(resolution,[],[f75,f24])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK6(sK2,X1),sK0) | ~r2_xboole_0(sK2,X1)) ) | ~spl7_7),
% 0.21/0.53    inference(resolution,[],[f66,f25])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl7_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f65])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl7_2 | ~spl7_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    $false | (spl7_2 | ~spl7_6)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f38,f63,f17])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl7_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f62])).
% 0.21/0.53  % (3948)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    spl7_6 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    spl7_6 | spl7_7 | ~spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f57,f50,f65,f62])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl7_5),
% 0.21/0.53    inference(resolution,[],[f54,f28])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK2)) ) | ~spl7_5),
% 0.21/0.53    inference(superposition,[],[f26,f52])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f14,f50])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f6])).
% 0.21/0.53  fof(f6,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ~spl7_3 | ~spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f13,f45,f41])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    sK0 != sK2 | sK1 != sK3),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ~spl7_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f16,f36])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ~spl7_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f15,f31])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (3967)------------------------------
% 0.21/0.53  % (3967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3967)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (3967)Memory used [KB]: 10746
% 0.21/0.53  % (3967)Time elapsed: 0.078 s
% 0.21/0.53  % (3967)------------------------------
% 0.21/0.53  % (3967)------------------------------
% 0.21/0.53  % (3966)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (3945)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (3945)Refutation not found, incomplete strategy% (3945)------------------------------
% 0.21/0.53  % (3945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3945)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3945)Memory used [KB]: 1663
% 0.21/0.53  % (3945)Time elapsed: 0.124 s
% 0.21/0.53  % (3945)------------------------------
% 0.21/0.53  % (3945)------------------------------
% 0.21/0.53  % (3944)Success in time 0.174 s
%------------------------------------------------------------------------------
