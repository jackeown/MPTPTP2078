%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 178 expanded)
%              Number of leaves         :   11 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  160 ( 361 expanded)
%              Number of equality atoms :  106 ( 287 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f101,f109,f115,f156,f192,f242,f316])).

fof(f316,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | spl2_7 ),
    inference(unit_resulting_resolution,[],[f11,f22,f79,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f20,f12,f12,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f79,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_7
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f22,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(definition_unfolding,[],[f10,f21,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f17,f12])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f10,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f11,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f242,plain,
    ( ~ spl2_1
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl2_1
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f62,f35,f55])).

fof(f55,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_1
  <=> ! [X1] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f35,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) ),
    inference(superposition,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
      | k1_xboole_0 != X2 ) ),
    inference(definition_unfolding,[],[f16,f12])).

% (32528)Termination reason: Refutation not found, incomplete strategy

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f3])).

% (32528)Memory used [KB]: 1663
% (32528)Time elapsed: 0.002 s
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

% (32528)------------------------------
% (32528)------------------------------
fof(f31,plain,(
    ! [X2,X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f15,f12])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f62,plain,
    ( k1_xboole_0 != sK1
    | spl2_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f192,plain,
    ( spl2_3
    | spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f187,f73,f54,f61])).

fof(f73,plain,
    ( spl2_6
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f187,plain,
    ( ! [X8] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X8)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = X8 )
    | ~ spl2_6 ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( ! [X8] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X8)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | k1_xboole_0 = X8 )
    | ~ spl2_6 ),
    inference(superposition,[],[f26,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f156,plain,
    ( ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f82,f35,f55])).

fof(f82,plain,
    ( k1_xboole_0 != sK0
    | ~ spl2_3 ),
    inference(superposition,[],[f11,f63])).

fof(f63,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f115,plain,
    ( spl2_8
    | spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f113,f98,f54,f94])).

fof(f94,plain,
    ( spl2_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f98,plain,
    ( spl2_9
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f113,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = X0 )
    | ~ spl2_9 ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = X0 )
    | ~ spl2_9 ),
    inference(superposition,[],[f26,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f109,plain,
    ( ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f82,f96])).

fof(f96,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f101,plain,
    ( spl2_8
    | spl2_9
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f92,f61,f98,f94])).

fof(f92,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | k1_xboole_0 = sK0
    | ~ spl2_3 ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | k1_xboole_0 = sK0
    | ~ spl2_3 ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | ~ spl2_3 ),
    inference(superposition,[],[f26,f83])).

fof(f83,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f81,f30])).

fof(f81,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f22,f63])).

fof(f80,plain,
    ( spl2_3
    | spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f51,f77,f73,f61])).

fof(f51,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f26,f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (32512)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.46  % (32512)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (32528)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (32528)Refutation not found, incomplete strategy% (32528)------------------------------
% 0.21/0.47  % (32528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f317,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f80,f101,f109,f115,f156,f192,f242,f316])).
% 0.21/0.47  fof(f316,plain,(
% 0.21/0.47    spl2_7),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f314])).
% 0.21/0.47  fof(f314,plain,(
% 0.21/0.47    $false | spl2_7),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f11,f22,f79,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 | X2 = X5) )),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f12,f12,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | X2 = X5) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl2_7 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 0.21/0.47    inference(definition_unfolding,[],[f10,f21,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f17,f12])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    sK0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f242,plain,(
% 0.21/0.47    ~spl2_1 | spl2_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f238])).
% 0.21/0.47  fof(f238,plain,(
% 0.21/0.47    $false | (~spl2_1 | spl2_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f62,f35,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1) ) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl2_1 <=> ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2)) )),
% 0.21/0.47    inference(superposition,[],[f31,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 | k1_xboole_0 != X2) )),
% 0.21/0.47    inference(definition_unfolding,[],[f16,f12])).
% 0.21/0.47  % (32528)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k1_xboole_0 != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  % (32528)Memory used [KB]: 1663
% 0.21/0.47  % (32528)Time elapsed: 0.002 s
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.21/0.47  % (32528)------------------------------
% 0.21/0.47  % (32528)------------------------------
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X2,X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2)) )),
% 0.21/0.47    inference(equality_resolution,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.47    inference(definition_unfolding,[],[f15,f12])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    k1_xboole_0 != sK1 | spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl2_3 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    spl2_3 | spl2_1 | ~spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f187,f73,f54,f61])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl2_6 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    ( ! [X8] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X8) | k1_xboole_0 = sK1 | k1_xboole_0 = X8) ) | ~spl2_6),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f185])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    ( ! [X8] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X8) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = X8) ) | ~spl2_6),
% 0.21/0.47    inference(superposition,[],[f26,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.21/0.47    inference(definition_unfolding,[],[f13,f12])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    ~spl2_1 | ~spl2_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    $false | (~spl2_1 | ~spl2_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f82,f35,f55])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    k1_xboole_0 != sK0 | ~spl2_3),
% 0.21/0.47    inference(superposition,[],[f11,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl2_8 | spl2_1 | ~spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f113,f98,f54,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl2_8 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl2_9 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = sK0 | k1_xboole_0 = X0) ) | ~spl2_9),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = X0) ) | ~spl2_9),
% 0.21/0.47    inference(superposition,[],[f26,f100])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f98])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ~spl2_3 | ~spl2_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    $false | (~spl2_3 | ~spl2_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f82,f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f94])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl2_8 | spl2_9 | ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f92,f61,f98,f94])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | k1_xboole_0 = sK0 | ~spl2_3),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f91])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | k1_xboole_0 = sK0 | ~spl2_3),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~spl2_3),
% 0.21/0.47    inference(superposition,[],[f26,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | ~spl2_3),
% 0.21/0.47    inference(forward_demodulation,[],[f81,f30])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) | ~spl2_3),
% 0.21/0.47    inference(superposition,[],[f22,f63])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl2_3 | spl2_6 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f51,f77,f73,f61])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | k1_xboole_0 = sK1),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.47    inference(superposition,[],[f26,f22])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (32512)------------------------------
% 0.21/0.47  % (32512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (32512)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (32512)Memory used [KB]: 6396
% 0.21/0.47  % (32512)Time elapsed: 0.052 s
% 0.21/0.47  % (32512)------------------------------
% 0.21/0.47  % (32512)------------------------------
% 0.21/0.47  % (32498)Success in time 0.116 s
%------------------------------------------------------------------------------
