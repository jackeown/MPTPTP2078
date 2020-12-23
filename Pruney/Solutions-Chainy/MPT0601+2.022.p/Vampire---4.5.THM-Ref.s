%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  82 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  130 ( 196 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f60,f70,f91,f95,f123])).

fof(f123,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f71,f110,f35])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f110,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(superposition,[],[f36,f100])).

fof(f100,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f96,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f96,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f48,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0))
        | k1_xboole_0 != k11_relat_1(sK1,X0) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_4
  <=> ! [X0] :
        ( k1_xboole_0 != k11_relat_1(sK1,X0)
        | r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f48,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl6_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f36,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f71,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f45,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl6_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f95,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f18,f87])).

fof(f87,plain,
    ( ~ v1_relat_1(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f91,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f52,f89,f85])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f23,f37])).

fof(f37,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f70,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f53,f44,f35])).

fof(f44,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f53,plain,
    ( r2_hidden(k4_tarski(sK0,sK2(k11_relat_1(sK1,sK0))),sK1)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f18,f51,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f51,plain,
    ( r2_hidden(sK2(k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f49,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f49,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f60,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f17,f47,f43])).

fof(f17,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f16,f47,f43])).

fof(f16,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.50  % (28067)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (28067)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (28084)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (28076)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f50,f60,f70,f91,f95,f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ~spl6_1 | ~spl6_2 | ~spl6_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    $false | (~spl6_1 | ~spl6_2 | ~spl6_4)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f71,f110,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k1_relat_1(sK1)) | (~spl6_2 | ~spl6_4)),
% 0.20/0.51    inference(superposition,[],[f36,f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | (~spl6_2 | ~spl6_4)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f96,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | (~spl6_2 | ~spl6_4)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f48,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0)) | k1_xboole_0 != k11_relat_1(sK1,X0)) ) | ~spl6_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl6_4 <=> ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl6_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    spl6_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.51    inference(equality_resolution,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1) | ~spl6_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f45,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.20/0.51    inference(equality_resolution,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    spl6_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl6_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    $false | spl6_3),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f18,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ~v1_relat_1(sK1) | spl6_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl6_3 <=> v1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    v1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ~spl6_3 | spl6_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f52,f89,f85])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0)) | ~v1_relat_1(sK1)) )),
% 0.20/0.51    inference(superposition,[],[f23,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0))) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f18,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl6_1 | spl6_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    $false | (spl6_1 | spl6_2)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f53,f44,f35])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f43])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK0,sK2(k11_relat_1(sK1,sK0))),sK1) | spl6_2),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f18,f51,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    r2_hidden(sK2(k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) | spl6_2),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f49,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl6_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f47])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ~spl6_1 | spl6_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f17,f47,f43])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    spl6_1 | ~spl6_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f16,f47,f43])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (28067)------------------------------
% 0.20/0.52  % (28067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28067)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (28067)Memory used [KB]: 6268
% 0.20/0.52  % (28067)Time elapsed: 0.115 s
% 0.20/0.52  % (28067)------------------------------
% 0.20/0.52  % (28067)------------------------------
% 0.20/0.52  % (28059)Success in time 0.159 s
%------------------------------------------------------------------------------
