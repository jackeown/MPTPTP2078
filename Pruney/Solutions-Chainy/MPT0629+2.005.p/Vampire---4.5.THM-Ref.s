%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 112 expanded)
%              Number of leaves         :   13 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  224 ( 386 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f48,f53,f82,f87,f101,f108,f146,f163])).

fof(f163,plain,
    ( ~ spl4_3
    | ~ spl4_9
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_9
    | spl4_13 ),
    inference(subsumption_resolution,[],[f161,f107])).

fof(f107,plain,
    ( r2_hidden(sK0,k9_relat_1(sK1,k2_relat_1(sK2)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_9
  <=> r2_hidden(sK0,k9_relat_1(sK1,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f161,plain,
    ( ~ r2_hidden(sK0,k9_relat_1(sK1,k2_relat_1(sK2)))
    | ~ spl4_3
    | spl4_13 ),
    inference(subsumption_resolution,[],[f159,f47])).

fof(f47,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f159,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k9_relat_1(sK1,k2_relat_1(sK2)))
    | spl4_13 ),
    inference(resolution,[],[f145,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f145,plain,
    ( ~ r2_hidden(sK3(sK0,k2_relat_1(sK2),sK1),k1_relat_1(sK1))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_13
  <=> r2_hidden(sK3(sK0,k2_relat_1(sK2),sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f146,plain,
    ( ~ spl4_13
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f128,f105,f79,f50,f45,f143])).

fof(f50,plain,
    ( spl4_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f79,plain,
    ( spl4_5
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f128,plain,
    ( ~ r2_hidden(sK3(sK0,k2_relat_1(sK2),sK1),k1_relat_1(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_9 ),
    inference(resolution,[],[f127,f107])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k9_relat_1(sK1,X0))
        | ~ r2_hidden(sK3(sK0,X0,sK1),k1_relat_1(sK1)) )
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(resolution,[],[f126,f81])).

fof(f81,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f126,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k2_relat_1(sK1))
        | ~ r2_hidden(sK3(X2,X3,sK1),k1_relat_1(sK1))
        | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f125,f47])).

fof(f125,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k2_relat_1(sK1))
        | ~ r2_hidden(sK3(X2,X3,sK1),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f123,f52])).

fof(f52,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f123,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k2_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(sK3(X2,X3,sK1),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f122])).

% (20728)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f122,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k2_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(sK3(X2,X3,sK1),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(sK3(X2,X3,sK1),k1_relat_1(sK1))
        | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(superposition,[],[f26,f113])).

fof(f113,plain,
    ( ! [X2,X1] :
        ( k1_funct_1(sK1,sK3(X1,X2,sK1)) = X1
        | ~ r2_hidden(sK3(X1,X2,sK1),k1_relat_1(sK1))
        | ~ r2_hidden(X1,k9_relat_1(sK1,X2)) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f76,f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK3(X0,X1,sK1),X0),sK1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | k1_funct_1(sK1,X2) = X3 )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f72,f47])).

fof(f72,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | k1_funct_1(sK1,X2) = X3 )
    | ~ spl4_4 ),
    inference(resolution,[],[f52,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f108,plain,
    ( spl4_9
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f102,f98,f84,f105])).

fof(f84,plain,
    ( spl4_6
  <=> r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f98,plain,
    ( spl4_8
  <=> k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f102,plain,
    ( r2_hidden(sK0,k9_relat_1(sK1,k2_relat_1(sK2)))
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(superposition,[],[f86,f100])).

fof(f100,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f86,plain,
    ( r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f101,plain,
    ( spl4_8
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f89,f45,f35,f98])).

fof(f35,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f89,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,
    ( ! [X7] :
        ( ~ v1_relat_1(X7)
        | k2_relat_1(k5_relat_1(sK2,X7)) = k9_relat_1(X7,k2_relat_1(sK2)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f37,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f37,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f87,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f17,f84])).

fof(f17,plain,(
    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
           => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_1)).

fof(f82,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f18,f79])).

fof(f18,plain,(
    ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:21:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (20718)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (20714)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (20724)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (20716)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (20714)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (20713)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f38,f48,f53,f82,f87,f101,f108,f146,f163])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    ~spl4_3 | ~spl4_9 | spl4_13),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    $false | (~spl4_3 | ~spl4_9 | spl4_13)),
% 0.22/0.48    inference(subsumption_resolution,[],[f161,f107])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    r2_hidden(sK0,k9_relat_1(sK1,k2_relat_1(sK2))) | ~spl4_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f105])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    spl4_9 <=> r2_hidden(sK0,k9_relat_1(sK1,k2_relat_1(sK2)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    ~r2_hidden(sK0,k9_relat_1(sK1,k2_relat_1(sK2))) | (~spl4_3 | spl4_13)),
% 0.22/0.48    inference(subsumption_resolution,[],[f159,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    v1_relat_1(sK1) | ~spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    spl4_3 <=> v1_relat_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ~v1_relat_1(sK1) | ~r2_hidden(sK0,k9_relat_1(sK1,k2_relat_1(sK2))) | spl4_13),
% 0.22/0.48    inference(resolution,[],[f145,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    ~r2_hidden(sK3(sK0,k2_relat_1(sK2),sK1),k1_relat_1(sK1)) | spl4_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f143])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    spl4_13 <=> r2_hidden(sK3(sK0,k2_relat_1(sK2),sK1),k1_relat_1(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    ~spl4_13 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f128,f105,f79,f50,f45,f143])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl4_4 <=> v1_funct_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl4_5 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    ~r2_hidden(sK3(sK0,k2_relat_1(sK2),sK1),k1_relat_1(sK1)) | (~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_9)),
% 0.22/0.48    inference(resolution,[],[f127,f107])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(sK0,k9_relat_1(sK1,X0)) | ~r2_hidden(sK3(sK0,X0,sK1),k1_relat_1(sK1))) ) | (~spl4_3 | ~spl4_4 | spl4_5)),
% 0.22/0.48    inference(resolution,[],[f126,f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f79])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ( ! [X2,X3] : (r2_hidden(X2,k2_relat_1(sK1)) | ~r2_hidden(sK3(X2,X3,sK1),k1_relat_1(sK1)) | ~r2_hidden(X2,k9_relat_1(sK1,X3))) ) | (~spl4_3 | ~spl4_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f125,f47])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    ( ! [X2,X3] : (r2_hidden(X2,k2_relat_1(sK1)) | ~r2_hidden(sK3(X2,X3,sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r2_hidden(X2,k9_relat_1(sK1,X3))) ) | (~spl4_3 | ~spl4_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f123,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    v1_funct_1(sK1) | ~spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f50])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ( ! [X2,X3] : (r2_hidden(X2,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~r2_hidden(sK3(X2,X3,sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r2_hidden(X2,k9_relat_1(sK1,X3))) ) | (~spl4_3 | ~spl4_4)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f122])).
% 0.22/0.48  % (20728)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ( ! [X2,X3] : (r2_hidden(X2,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~r2_hidden(sK3(X2,X3,sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r2_hidden(sK3(X2,X3,sK1),k1_relat_1(sK1)) | ~r2_hidden(X2,k9_relat_1(sK1,X3))) ) | (~spl4_3 | ~spl4_4)),
% 0.22/0.48    inference(superposition,[],[f26,f113])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    ( ! [X2,X1] : (k1_funct_1(sK1,sK3(X1,X2,sK1)) = X1 | ~r2_hidden(sK3(X1,X2,sK1),k1_relat_1(sK1)) | ~r2_hidden(X1,k9_relat_1(sK1,X2))) ) | (~spl4_3 | ~spl4_4)),
% 0.22/0.48    inference(resolution,[],[f76,f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,sK1),X0),sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) ) | ~spl4_3),
% 0.22/0.48    inference(resolution,[],[f47,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | ~r2_hidden(X2,k1_relat_1(sK1)) | k1_funct_1(sK1,X2) = X3) ) | (~spl4_3 | ~spl4_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f72,f47])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~v1_relat_1(sK1) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3) ) | ~spl4_4),
% 0.22/0.48    inference(resolution,[],[f52,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) = X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    spl4_9 | ~spl4_6 | ~spl4_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f102,f98,f84,f105])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl4_6 <=> r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    spl4_8 <=> k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    r2_hidden(sK0,k9_relat_1(sK1,k2_relat_1(sK2))) | (~spl4_6 | ~spl4_8)),
% 0.22/0.48    inference(superposition,[],[f86,f100])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2)) | ~spl4_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f98])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) | ~spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f84])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    spl4_8 | ~spl4_1 | ~spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f89,f45,f35,f98])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    spl4_1 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2)) | (~spl4_1 | ~spl4_3)),
% 0.22/0.48    inference(resolution,[],[f57,f47])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X7] : (~v1_relat_1(X7) | k2_relat_1(k5_relat_1(sK2,X7)) = k9_relat_1(X7,k2_relat_1(sK2))) ) | ~spl4_1),
% 0.22/0.48    inference(resolution,[],[f37,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f35])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    spl4_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f17,f84])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : ((~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_1)).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ~spl4_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f79])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f50])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    v1_funct_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f45])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f15,f35])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (20714)------------------------------
% 0.22/0.48  % (20714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (20714)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (20714)Memory used [KB]: 10618
% 0.22/0.48  % (20714)Time elapsed: 0.060 s
% 0.22/0.48  % (20714)------------------------------
% 0.22/0.48  % (20714)------------------------------
% 0.22/0.48  % (20710)Success in time 0.117 s
%------------------------------------------------------------------------------
