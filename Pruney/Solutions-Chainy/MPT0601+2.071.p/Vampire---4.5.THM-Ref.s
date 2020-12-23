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
% DateTime   : Thu Dec  3 12:51:16 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   59 (  85 expanded)
%              Number of leaves         :   13 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  149 ( 214 expanded)
%              Number of equality atoms :   16 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f42,f105,f112,f119,f126,f164])).

fof(f164,plain,
    ( ~ spl4_1
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f134,f40])).

fof(f40,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f134,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl4_7 ),
    inference(superposition,[],[f127,f45])).

fof(f45,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f22,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f127,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k10_relat_1(sK1,X0))
    | ~ spl4_7 ),
    inference(resolution,[],[f125,f43])).

fof(f43,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f125,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK0,X1,sK1),k1_xboole_0)
        | ~ r2_hidden(sK0,k10_relat_1(sK1,X1)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_7
  <=> ! [X1] :
        ( r2_hidden(sK3(sK0,X1,sK1),k1_xboole_0)
        | ~ r2_hidden(sK0,k10_relat_1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f126,plain,
    ( ~ spl4_5
    | spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f121,f117,f124,f103])).

fof(f103,plain,
    ( spl4_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f117,plain,
    ( spl4_6
  <=> ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(k4_tarski(sK0,X2),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f121,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK0,X1,sK1),k1_xboole_0)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(sK0,k10_relat_1(sK1,X1)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f118,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f118,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k4_tarski(sK0,X2),sK1)
        | r2_hidden(X2,k1_xboole_0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,
    ( ~ spl4_5
    | spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f115,f37,f117,f103])).

fof(f37,plain,
    ( spl4_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f115,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(sK0,X2),sK1) )
    | ~ spl4_2 ),
    inference(superposition,[],[f32,f38])).

fof(f38,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f112,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f104,f20])).

fof(f104,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( spl4_2
    | ~ spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f99,f34,f103,f37])).

fof(f99,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k11_relat_1(sK1,sK0)
    | spl4_1 ),
    inference(resolution,[],[f60,f35])).

fof(f35,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k11_relat_1(X0,X1) ) ),
    inference(resolution,[],[f49,f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f49,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k11_relat_1(X4,X5))
      | ~ v1_relat_1(X4)
      | r2_hidden(X5,k1_relat_1(X4)) ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k11_relat_1(X4,X5))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X4)
      | r2_hidden(X5,k1_relat_1(X4)) ) ),
    inference(resolution,[],[f31,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f18,f37,f34])).

fof(f18,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f19,f37,f34])).

fof(f19,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:01:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.52  % (19994)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.23/0.52  % (19994)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f165,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(avatar_sat_refutation,[],[f39,f42,f105,f112,f119,f126,f164])).
% 0.23/0.52  fof(f164,plain,(
% 0.23/0.52    ~spl4_1 | ~spl4_7),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f162])).
% 0.23/0.52  fof(f162,plain,(
% 0.23/0.52    $false | (~spl4_1 | ~spl4_7)),
% 0.23/0.52    inference(resolution,[],[f134,f40])).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl4_1),
% 0.23/0.52    inference(avatar_component_clause,[],[f34])).
% 0.23/0.52  fof(f34,plain,(
% 0.23/0.52    spl4_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.52  fof(f134,plain,(
% 0.23/0.52    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~spl4_7),
% 0.23/0.52    inference(superposition,[],[f127,f45])).
% 0.23/0.52  fof(f45,plain,(
% 0.23/0.52    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.23/0.52    inference(resolution,[],[f22,f20])).
% 0.23/0.52  fof(f20,plain,(
% 0.23/0.52    v1_relat_1(sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f10])).
% 0.23/0.52  fof(f10,plain,(
% 0.23/0.52    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.23/0.52    inference(ennf_transformation,[],[f9])).
% 0.23/0.52  fof(f9,negated_conjecture,(
% 0.23/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.23/0.52    inference(negated_conjecture,[],[f8])).
% 0.23/0.52  fof(f8,conjecture,(
% 0.23/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.23/0.52  fof(f22,plain,(
% 0.23/0.52    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f11])).
% 0.23/0.52  fof(f11,plain,(
% 0.23/0.52    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.52    inference(ennf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.23/0.52  fof(f127,plain,(
% 0.23/0.52    ( ! [X0] : (~r2_hidden(sK0,k10_relat_1(sK1,X0))) ) | ~spl4_7),
% 0.23/0.52    inference(resolution,[],[f125,f43])).
% 0.23/0.52  fof(f43,plain,(
% 0.23/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.52    inference(resolution,[],[f24,f21])).
% 0.23/0.52  fof(f21,plain,(
% 0.23/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f2])).
% 0.23/0.52  fof(f2,axiom,(
% 0.23/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.23/0.52  fof(f24,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f13])).
% 0.23/0.52  fof(f13,plain,(
% 0.23/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.52    inference(ennf_transformation,[],[f3])).
% 0.23/0.52  fof(f3,axiom,(
% 0.23/0.52    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.23/0.52  fof(f125,plain,(
% 0.23/0.52    ( ! [X1] : (r2_hidden(sK3(sK0,X1,sK1),k1_xboole_0) | ~r2_hidden(sK0,k10_relat_1(sK1,X1))) ) | ~spl4_7),
% 0.23/0.52    inference(avatar_component_clause,[],[f124])).
% 0.23/0.52  fof(f124,plain,(
% 0.23/0.52    spl4_7 <=> ! [X1] : (r2_hidden(sK3(sK0,X1,sK1),k1_xboole_0) | ~r2_hidden(sK0,k10_relat_1(sK1,X1)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.23/0.52  fof(f126,plain,(
% 0.23/0.52    ~spl4_5 | spl4_7 | ~spl4_6),
% 0.23/0.52    inference(avatar_split_clause,[],[f121,f117,f124,f103])).
% 0.23/0.52  fof(f103,plain,(
% 0.23/0.52    spl4_5 <=> v1_relat_1(sK1)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.23/0.52  fof(f117,plain,(
% 0.23/0.52    spl4_6 <=> ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(k4_tarski(sK0,X2),sK1))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.23/0.52  fof(f121,plain,(
% 0.23/0.52    ( ! [X1] : (r2_hidden(sK3(sK0,X1,sK1),k1_xboole_0) | ~v1_relat_1(sK1) | ~r2_hidden(sK0,k10_relat_1(sK1,X1))) ) | ~spl4_6),
% 0.23/0.52    inference(resolution,[],[f118,f28])).
% 0.23/0.52  fof(f28,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f16])).
% 0.23/0.52  fof(f16,plain,(
% 0.23/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.23/0.52    inference(ennf_transformation,[],[f4])).
% 0.23/0.52  fof(f4,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.23/0.52  fof(f118,plain,(
% 0.23/0.52    ( ! [X2] : (~r2_hidden(k4_tarski(sK0,X2),sK1) | r2_hidden(X2,k1_xboole_0)) ) | ~spl4_6),
% 0.23/0.52    inference(avatar_component_clause,[],[f117])).
% 0.23/0.52  fof(f119,plain,(
% 0.23/0.52    ~spl4_5 | spl4_6 | ~spl4_2),
% 0.23/0.52    inference(avatar_split_clause,[],[f115,f37,f117,f103])).
% 0.23/0.52  fof(f37,plain,(
% 0.23/0.52    spl4_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.52  fof(f115,plain,(
% 0.23/0.52    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(sK0,X2),sK1)) ) | ~spl4_2),
% 0.23/0.52    inference(superposition,[],[f32,f38])).
% 0.23/0.52  fof(f38,plain,(
% 0.23/0.52    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl4_2),
% 0.23/0.52    inference(avatar_component_clause,[],[f37])).
% 0.23/0.52  fof(f32,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f17])).
% 0.23/0.52  fof(f17,plain,(
% 0.23/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.23/0.52    inference(ennf_transformation,[],[f6])).
% 0.23/0.52  fof(f6,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.23/0.52  fof(f112,plain,(
% 0.23/0.52    spl4_5),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f111])).
% 0.23/0.52  fof(f111,plain,(
% 0.23/0.52    $false | spl4_5),
% 0.23/0.52    inference(resolution,[],[f104,f20])).
% 0.23/0.52  fof(f104,plain,(
% 0.23/0.52    ~v1_relat_1(sK1) | spl4_5),
% 0.23/0.52    inference(avatar_component_clause,[],[f103])).
% 0.23/0.52  fof(f105,plain,(
% 0.23/0.52    spl4_2 | ~spl4_5 | spl4_1),
% 0.23/0.52    inference(avatar_split_clause,[],[f99,f34,f103,f37])).
% 0.23/0.52  fof(f99,plain,(
% 0.23/0.52    ~v1_relat_1(sK1) | k1_xboole_0 = k11_relat_1(sK1,sK0) | spl4_1),
% 0.23/0.52    inference(resolution,[],[f60,f35])).
% 0.23/0.52  fof(f35,plain,(
% 0.23/0.52    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl4_1),
% 0.23/0.52    inference(avatar_component_clause,[],[f34])).
% 0.23/0.52  fof(f60,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k11_relat_1(X0,X1)) )),
% 0.23/0.52    inference(resolution,[],[f49,f23])).
% 0.23/0.52  fof(f23,plain,(
% 0.23/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.23/0.52    inference(cnf_transformation,[],[f12])).
% 0.23/0.52  fof(f12,plain,(
% 0.23/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.23/0.52    inference(ennf_transformation,[],[f1])).
% 0.23/0.52  fof(f1,axiom,(
% 0.23/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.23/0.52  fof(f49,plain,(
% 0.23/0.52    ( ! [X4,X5,X3] : (~r2_hidden(X3,k11_relat_1(X4,X5)) | ~v1_relat_1(X4) | r2_hidden(X5,k1_relat_1(X4))) )),
% 0.23/0.52    inference(duplicate_literal_removal,[],[f47])).
% 0.23/0.52  fof(f47,plain,(
% 0.23/0.52    ( ! [X4,X5,X3] : (~r2_hidden(X3,k11_relat_1(X4,X5)) | ~v1_relat_1(X4) | ~v1_relat_1(X4) | r2_hidden(X5,k1_relat_1(X4))) )),
% 0.23/0.52    inference(resolution,[],[f31,f25])).
% 0.23/0.52  fof(f25,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f15])).
% 0.23/0.52  fof(f15,plain,(
% 0.23/0.52    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.23/0.52    inference(flattening,[],[f14])).
% 0.23/0.52  fof(f14,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.23/0.52    inference(ennf_transformation,[],[f7])).
% 0.23/0.52  fof(f7,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.23/0.52  fof(f31,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f17])).
% 0.23/0.52  fof(f42,plain,(
% 0.23/0.52    spl4_1 | ~spl4_2),
% 0.23/0.52    inference(avatar_split_clause,[],[f18,f37,f34])).
% 0.23/0.52  fof(f18,plain,(
% 0.23/0.52    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.23/0.52    inference(cnf_transformation,[],[f10])).
% 0.23/0.52  fof(f39,plain,(
% 0.23/0.52    ~spl4_1 | spl4_2),
% 0.23/0.52    inference(avatar_split_clause,[],[f19,f37,f34])).
% 0.23/0.52  fof(f19,plain,(
% 0.23/0.52    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.23/0.52    inference(cnf_transformation,[],[f10])).
% 0.23/0.52  % SZS output end Proof for theBenchmark
% 0.23/0.52  % (19994)------------------------------
% 0.23/0.52  % (19994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (19994)Termination reason: Refutation
% 0.23/0.52  
% 0.23/0.52  % (19994)Memory used [KB]: 10746
% 0.23/0.52  % (19994)Time elapsed: 0.066 s
% 0.23/0.52  % (19994)------------------------------
% 0.23/0.52  % (19994)------------------------------
% 0.23/0.52  % (19981)Success in time 0.152 s
%------------------------------------------------------------------------------
