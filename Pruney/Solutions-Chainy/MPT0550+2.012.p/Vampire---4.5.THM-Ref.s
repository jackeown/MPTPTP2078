%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  92 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  181 ( 301 expanded)
%              Number of equality atoms :   39 (  86 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f86,f92,f99,f107])).

fof(f107,plain,
    ( ~ spl2_2
    | spl2_3
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl2_2
    | spl2_3
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f41,f46,f98,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f98,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_12
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f46,plain,
    ( k1_xboole_0 != sK0
    | spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f41,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f99,plain,
    ( spl2_12
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f94,f90,f49,f96])).

fof(f49,plain,
    ( spl2_4
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f90,plain,
    ( spl2_11
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ r1_tarski(X0,k1_relat_1(sK1))
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f94,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f93,f51])).

fof(f51,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f93,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | v1_xboole_0(sK0)
    | ~ spl2_11 ),
    inference(resolution,[],[f91,f31])).

fof(f31,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_tarski(X0,k1_relat_1(sK1))
        | v1_xboole_0(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,
    ( spl2_11
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f88,f84,f54,f90])).

fof(f54,plain,
    ( spl2_5
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f84,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | v1_xboole_0(X0)
        | k1_xboole_0 != k9_relat_1(sK1,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f88,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ r1_tarski(X0,k1_relat_1(sK1))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_xboole_0(X0)
        | ~ r1_tarski(X0,k1_relat_1(sK1))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(superposition,[],[f85,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k9_relat_1(sK1,X1)
        | v1_xboole_0(X0)
        | ~ r1_tarski(X0,k1_relat_1(sK1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( spl2_10
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f82,f34,f84])).

fof(f34,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | v1_xboole_0(X0)
        | k1_xboole_0 != k9_relat_1(sK1,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_1 ),
    inference(resolution,[],[f76,f36])).

fof(f36,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | v1_xboole_0(X0)
      | k1_xboole_0 != k9_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f30,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f57,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK1,sK0)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f52,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f37,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:43:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (28359)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.45  % (28369)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.45  % (28359)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f86,f92,f99,f107])).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    ~spl2_2 | spl2_3 | ~spl2_12),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f102])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    $false | (~spl2_2 | spl2_3 | ~spl2_12)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f41,f46,f98,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    v1_xboole_0(sK0) | ~spl2_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f96])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    spl2_12 <=> v1_xboole_0(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    k1_xboole_0 != sK0 | spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    spl2_3 <=> k1_xboole_0 = sK0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    v1_xboole_0(k1_xboole_0) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl2_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    spl2_12 | ~spl2_4 | ~spl2_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f94,f90,f49,f96])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    spl2_4 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    spl2_11 <=> ! [X0] : (v1_xboole_0(X0) | ~r1_tarski(X0,k1_relat_1(sK1)) | ~r1_tarski(X0,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    v1_xboole_0(sK0) | (~spl2_4 | ~spl2_11)),
% 0.20/0.46    inference(subsumption_resolution,[],[f93,f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f49])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    ~r1_tarski(sK0,k1_relat_1(sK1)) | v1_xboole_0(sK0) | ~spl2_11),
% 0.20/0.46    inference(resolution,[],[f91,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.46    inference(equality_resolution,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.46    inference(flattening,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.46    inference(nnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(X0,sK0) | ~r1_tarski(X0,k1_relat_1(sK1)) | v1_xboole_0(X0)) ) | ~spl2_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f90])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    spl2_11 | ~spl2_5 | ~spl2_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f88,f84,f54,f90])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    spl2_5 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    spl2_10 <=> ! [X1,X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | v1_xboole_0(X0) | k1_xboole_0 != k9_relat_1(sK1,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    ( ! [X0] : (v1_xboole_0(X0) | ~r1_tarski(X0,k1_relat_1(sK1)) | ~r1_tarski(X0,sK0)) ) | (~spl2_5 | ~spl2_10)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f87])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_xboole_0(X0) | ~r1_tarski(X0,k1_relat_1(sK1)) | ~r1_tarski(X0,sK0)) ) | (~spl2_5 | ~spl2_10)),
% 0.20/0.46    inference(superposition,[],[f85,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f54])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(sK1,X1) | v1_xboole_0(X0) | ~r1_tarski(X0,k1_relat_1(sK1)) | ~r1_tarski(X0,X1)) ) | ~spl2_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f84])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    spl2_10 | ~spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f82,f34,f84])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    spl2_1 <=> v1_relat_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(sK1)) | v1_xboole_0(X0) | k1_xboole_0 != k9_relat_1(sK1,X1) | ~r1_tarski(X0,X1)) ) | ~spl2_1),
% 0.20/0.46    inference(resolution,[],[f76,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f34])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | v1_xboole_0(X0) | k1_xboole_0 != k9_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(resolution,[],[f30,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(nnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 0.20/0.46    inference(flattening,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl2_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f54])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.46    inference(negated_conjecture,[],[f6])).
% 0.20/0.46  fof(f6,conjecture,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f49])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ~spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f44])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    k1_xboole_0 != sK0),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f39])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    v1_xboole_0(k1_xboole_0)),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    v1_xboole_0(k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f34])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (28359)------------------------------
% 0.20/0.46  % (28359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (28359)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (28359)Memory used [KB]: 6140
% 0.20/0.46  % (28359)Time elapsed: 0.057 s
% 0.20/0.46  % (28359)------------------------------
% 0.20/0.46  % (28359)------------------------------
% 0.20/0.46  % (28356)Success in time 0.11 s
%------------------------------------------------------------------------------
