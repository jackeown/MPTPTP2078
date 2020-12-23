%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 125 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  282 ( 472 expanded)
%              Number of equality atoms :   40 (  72 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f55,f75,f79,f85,f91,f97,f107,f117,f151,f160])).

fof(f160,plain,
    ( ~ spl3_2
    | spl3_3
    | spl3_4
    | spl3_5
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl3_2
    | spl3_3
    | spl3_4
    | spl3_5
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f158,f46])).

fof(f46,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_5
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f158,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl3_2
    | spl3_3
    | spl3_4
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f157,f42])).

fof(f42,plain,
    ( sK0 != sK1
    | spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f157,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | ~ spl3_2
    | spl3_3
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f156,f34])).

fof(f34,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f156,plain,
    ( ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | spl3_3
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f154,f38])).

fof(f38,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f154,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(resolution,[],[f150,f116])).

fof(f116,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | sK0 = X1
        | r2_xboole_0(X1,sK0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_19
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | sK0 = X1
        | r2_xboole_0(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f150,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,X0)
        | r2_xboole_0(X0,sK1)
        | ~ v3_ordinal1(X0)
        | sK1 = X0 )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl3_27
  <=> ! [X0] :
        ( sK1 = X0
        | r2_xboole_0(X0,sK1)
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f151,plain,
    ( spl3_27
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f113,f105,f83,f29,f149])).

fof(f29,plain,
    ( spl3_1
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f83,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(X1)
        | r2_hidden(X0,X1)
        | X0 = X1
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f105,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sK1 = X0
        | r2_xboole_0(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f113,plain,
    ( ! [X0] :
        ( sK1 = X0
        | r2_xboole_0(X0,sK1)
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK1,X0) )
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f112,f30])).

fof(f30,plain,
    ( v3_ordinal1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f112,plain,
    ( ! [X0] :
        ( sK1 = X0
        | r2_xboole_0(X0,sK1)
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK1,X0)
        | ~ v3_ordinal1(sK1) )
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( ! [X0] :
        ( sK1 = X0
        | r2_xboole_0(X0,sK1)
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK1,X0)
        | sK1 = X0
        | ~ v3_ordinal1(sK1) )
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(resolution,[],[f106,f84])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1)
        | r2_hidden(X0,X1)
        | X0 = X1
        | ~ v3_ordinal1(X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f83])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sK1 = X0
        | r2_xboole_0(X0,sK1) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f105])).

fof(f117,plain,
    ( spl3_19
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f99,f95,f33,f115])).

fof(f95,plain,
    ( spl3_16
  <=> ! [X3,X2] :
        ( r2_xboole_0(X2,X3)
        | ~ r2_hidden(X2,X3)
        | X2 = X3
        | ~ v3_ordinal1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f99,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | sK0 = X1
        | r2_xboole_0(X1,sK0) )
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(resolution,[],[f96,f34])).

fof(f96,plain,
    ( ! [X2,X3] :
        ( ~ v3_ordinal1(X3)
        | ~ r2_hidden(X2,X3)
        | X2 = X3
        | r2_xboole_0(X2,X3) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f95])).

fof(f107,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f98,f95,f29,f105])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sK1 = X0
        | r2_xboole_0(X0,sK1) )
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(resolution,[],[f96,f30])).

fof(f97,plain,
    ( spl3_16
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f93,f89,f53,f95])).

fof(f53,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | v1_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f89,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( X0 = X1
        | r2_xboole_0(X0,X1)
        | ~ r2_hidden(X0,X1)
        | ~ v1_ordinal1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f93,plain,
    ( ! [X2,X3] :
        ( r2_xboole_0(X2,X3)
        | ~ r2_hidden(X2,X3)
        | X2 = X3
        | ~ v3_ordinal1(X3) )
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(resolution,[],[f90,f54])).

fof(f54,plain,
    ( ! [X0] :
        ( v1_ordinal1(X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ v1_ordinal1(X1)
        | r2_xboole_0(X0,X1)
        | ~ r2_hidden(X0,X1)
        | X0 = X1 )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,
    ( spl3_15
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f80,f77,f73,f89])).

fof(f73,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | r1_tarski(X1,X0)
        | ~ v1_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f77,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | r2_xboole_0(X0,X1)
        | ~ r2_hidden(X0,X1)
        | ~ v1_ordinal1(X1) )
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(resolution,[],[f78,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,X0)
        | ~ r2_hidden(X1,X0)
        | ~ v1_ordinal1(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f73])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f77])).

fof(f85,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f20,f83])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f79,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f26,f77])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f75,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f21,f73])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f55,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f18,f53])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f47,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f16,f45])).

fof(f16,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ~ ( ~ r2_xboole_0(X1,X0)
                & X0 != X1
                & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).

fof(f43,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f15,f41])).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f14,f37])).

fof(f14,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:22:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (3821)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (3821)Refutation not found, incomplete strategy% (3821)------------------------------
% 0.21/0.48  % (3821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3821)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3821)Memory used [KB]: 10490
% 0.21/0.48  % (3821)Time elapsed: 0.060 s
% 0.21/0.48  % (3821)------------------------------
% 0.21/0.48  % (3821)------------------------------
% 0.21/0.48  % (3829)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (3824)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (3829)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f55,f75,f79,f85,f91,f97,f107,f117,f151,f160])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~spl3_2 | spl3_3 | spl3_4 | spl3_5 | ~spl3_19 | ~spl3_27),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    $false | (~spl3_2 | spl3_3 | spl3_4 | spl3_5 | ~spl3_19 | ~spl3_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f158,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ~r2_xboole_0(sK1,sK0) | spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl3_5 <=> r2_xboole_0(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    r2_xboole_0(sK1,sK0) | (~spl3_2 | spl3_3 | spl3_4 | ~spl3_19 | ~spl3_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f157,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    sK0 != sK1 | spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl3_4 <=> sK0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    sK0 = sK1 | r2_xboole_0(sK1,sK0) | (~spl3_2 | spl3_3 | ~spl3_19 | ~spl3_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f156,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v3_ordinal1(sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    spl3_2 <=> v3_ordinal1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ~v3_ordinal1(sK0) | sK0 = sK1 | r2_xboole_0(sK1,sK0) | (spl3_3 | ~spl3_19 | ~spl3_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f154,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ~r2_xboole_0(sK0,sK1) | spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    spl3_3 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    r2_xboole_0(sK0,sK1) | ~v3_ordinal1(sK0) | sK0 = sK1 | r2_xboole_0(sK1,sK0) | (~spl3_19 | ~spl3_27)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f153])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    r2_xboole_0(sK0,sK1) | ~v3_ordinal1(sK0) | sK0 = sK1 | sK0 = sK1 | r2_xboole_0(sK1,sK0) | (~spl3_19 | ~spl3_27)),
% 0.21/0.49    inference(resolution,[],[f150,f116])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | sK0 = X1 | r2_xboole_0(X1,sK0)) ) | ~spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f115])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl3_19 <=> ! [X1] : (~r2_hidden(X1,sK0) | sK0 = X1 | r2_xboole_0(X1,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1,X0) | r2_xboole_0(X0,sK1) | ~v3_ordinal1(X0) | sK1 = X0) ) | ~spl3_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f149])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    spl3_27 <=> ! [X0] : (sK1 = X0 | r2_xboole_0(X0,sK1) | ~v3_ordinal1(X0) | r2_hidden(sK1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    spl3_27 | ~spl3_1 | ~spl3_14 | ~spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f113,f105,f83,f29,f149])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    spl3_1 <=> v3_ordinal1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl3_14 <=> ! [X1,X0] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl3_18 <=> ! [X0] : (~r2_hidden(X0,sK1) | sK1 = X0 | r2_xboole_0(X0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 = X0 | r2_xboole_0(X0,sK1) | ~v3_ordinal1(X0) | r2_hidden(sK1,X0)) ) | (~spl3_1 | ~spl3_14 | ~spl3_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f112,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v3_ordinal1(sK1) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f29])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 = X0 | r2_xboole_0(X0,sK1) | ~v3_ordinal1(X0) | r2_hidden(sK1,X0) | ~v3_ordinal1(sK1)) ) | (~spl3_14 | ~spl3_18)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 = X0 | r2_xboole_0(X0,sK1) | ~v3_ordinal1(X0) | r2_hidden(sK1,X0) | sK1 = X0 | ~v3_ordinal1(sK1)) ) | (~spl3_14 | ~spl3_18)),
% 0.21/0.49    inference(resolution,[],[f106,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X0)) ) | ~spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK1) | sK1 = X0 | r2_xboole_0(X0,sK1)) ) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f105])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl3_19 | ~spl3_2 | ~spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f99,f95,f33,f115])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl3_16 <=> ! [X3,X2] : (r2_xboole_0(X2,X3) | ~r2_hidden(X2,X3) | X2 = X3 | ~v3_ordinal1(X3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | sK0 = X1 | r2_xboole_0(X1,sK0)) ) | (~spl3_2 | ~spl3_16)),
% 0.21/0.49    inference(resolution,[],[f96,f34])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~v3_ordinal1(X3) | ~r2_hidden(X2,X3) | X2 = X3 | r2_xboole_0(X2,X3)) ) | ~spl3_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f95])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl3_18 | ~spl3_1 | ~spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f95,f29,f105])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK1) | sK1 = X0 | r2_xboole_0(X0,sK1)) ) | (~spl3_1 | ~spl3_16)),
% 0.21/0.49    inference(resolution,[],[f96,f30])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl3_16 | ~spl3_7 | ~spl3_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f93,f89,f53,f95])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl3_7 <=> ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl3_15 <=> ! [X1,X0] : (X0 = X1 | r2_xboole_0(X0,X1) | ~r2_hidden(X0,X1) | ~v1_ordinal1(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_xboole_0(X2,X3) | ~r2_hidden(X2,X3) | X2 = X3 | ~v3_ordinal1(X3)) ) | (~spl3_7 | ~spl3_15)),
% 0.21/0.49    inference(resolution,[],[f90,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) ) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_ordinal1(X1) | r2_xboole_0(X0,X1) | ~r2_hidden(X0,X1) | X0 = X1) ) | ~spl3_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl3_15 | ~spl3_12 | ~spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f80,f77,f73,f89])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl3_12 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | r1_tarski(X1,X0) | ~v1_ordinal1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl3_13 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0,X1] : (X0 = X1 | r2_xboole_0(X0,X1) | ~r2_hidden(X0,X1) | ~v1_ordinal1(X1)) ) | (~spl3_12 | ~spl3_13)),
% 0.21/0.49    inference(resolution,[],[f78,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) ) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) ) | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f83])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f77])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f73])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_tarski(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f18,f53])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ~spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f45])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ~r2_xboole_0(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f41])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    sK0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f14,f37])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ~r2_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f17,f33])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    v3_ordinal1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f13,f29])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    v3_ordinal1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (3829)------------------------------
% 0.21/0.49  % (3829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3823)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (3829)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (3829)Memory used [KB]: 10618
% 0.21/0.49  % (3829)Time elapsed: 0.065 s
% 0.21/0.49  % (3829)------------------------------
% 0.21/0.49  % (3829)------------------------------
% 0.21/0.49  % (3819)Success in time 0.129 s
%------------------------------------------------------------------------------
