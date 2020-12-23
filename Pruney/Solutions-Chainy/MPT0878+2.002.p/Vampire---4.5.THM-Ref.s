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
% DateTime   : Thu Dec  3 12:58:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  86 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :  114 ( 190 expanded)
%              Number of equality atoms :   63 ( 117 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f62,f68,f76,f99,f113,f133])).

fof(f133,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl2_3
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f56,f56,f53,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f53,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_3
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f56,plain,
    ( k1_xboole_0 != sK1
    | spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f113,plain,
    ( spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl2_6
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f75,f75,f98,f14])).

fof(f98,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_7
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f75,plain,
    ( k1_xboole_0 != sK0
    | spl2_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f99,plain,
    ( spl2_7
    | spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f91,f59,f73,f96])).

fof(f59,plain,
    ( spl2_5
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f91,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f84])).

fof(f84,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_5 ),
    inference(superposition,[],[f14,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f76,plain,
    ( ~ spl2_6
    | spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f70,f55,f28,f73])).

fof(f28,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f70,plain,
    ( k1_xboole_0 != sK0
    | spl2_1
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f30,f57])).

fof(f57,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f30,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f68,plain,
    ( spl2_1
    | ~ spl2_2
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f30,f35,f61,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f20,f17,f17,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f61,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f35,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_2
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f62,plain,
    ( spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f43,f33,f59,f55,f51])).

fof(f43,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f14,f35])).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f33])).

fof(f21,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(definition_unfolding,[],[f11,f17,f17])).

fof(f11,plain,(
    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

fof(f31,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f12,f28])).

fof(f12,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:12:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (10734)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.51  % (10710)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (10722)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (10707)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (10734)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f31,f36,f62,f68,f76,f99,f113,f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ~spl2_3 | spl2_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    $false | (~spl2_3 | spl2_4)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f56,f56,f53,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | ~spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl2_3 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl2_4 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl2_6 | ~spl2_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    $false | (spl2_6 | ~spl2_7)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f75,f75,f98,f14])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | ~spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl2_7 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl2_6 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl2_7 | spl2_6 | ~spl2_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f91,f59,f73,f96])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl2_5 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | ~spl2_5),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | ~spl2_5),
% 0.21/0.52    inference(superposition,[],[f14,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | ~spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f59])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ~spl2_6 | spl2_1 | ~spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f70,f55,f28,f73])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    spl2_1 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | (spl2_1 | ~spl2_4)),
% 0.21/0.52    inference(backward_demodulation,[],[f30,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f55])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    sK0 != sK1 | spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f28])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl2_1 | ~spl2_2 | spl2_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    $false | (spl2_1 | ~spl2_2 | spl2_5)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f30,f35,f61,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X2 = X5) )),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f17,f17,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | X2 = X5) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f59])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | ~spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    spl2_2 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl2_3 | spl2_4 | ~spl2_5 | ~spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f33,f59,f55,f51])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | ~spl2_2),
% 0.21/0.52    inference(superposition,[],[f14,f35])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f21,f33])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f11,f17,f17])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1] : (X0 != X1 & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ~spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f12,f28])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    sK0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (10734)------------------------------
% 0.21/0.52  % (10734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10734)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (10734)Memory used [KB]: 10746
% 0.21/0.52  % (10734)Time elapsed: 0.110 s
% 0.21/0.52  % (10734)------------------------------
% 0.21/0.52  % (10734)------------------------------
% 0.21/0.52  % (10702)Success in time 0.161 s
%------------------------------------------------------------------------------
