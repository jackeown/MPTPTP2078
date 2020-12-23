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
% DateTime   : Thu Dec  3 12:38:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 190 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  258 ( 577 expanded)
%              Number of equality atoms :   90 ( 317 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1572,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f61,f66,f252,f333,f464,f1342,f1371,f1562,f1571])).

% (25257)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f1571,plain,
    ( spl6_2
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f1570])).

fof(f1570,plain,
    ( $false
    | spl6_2
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f285,f1527])).

% (25253)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f1527,plain,
    ( sK0 != sK5(sK0,sK1)
    | spl6_2
    | ~ spl6_7 ),
    inference(trivial_inequality_removal,[],[f1521])).

fof(f1521,plain,
    ( sK0 != sK5(sK0,sK1)
    | sK1 != sK1
    | spl6_2
    | ~ spl6_7 ),
    inference(resolution,[],[f1402,f251])).

fof(f251,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl6_7
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1402,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | sK0 != sK5(sK0,X1)
        | sK1 != X1 )
    | spl6_2 ),
    inference(inner_rewriting,[],[f1401])).

fof(f1401,plain,
    ( ! [X1] :
        ( sK1 != X1
        | sK0 != sK5(sK0,X1)
        | ~ r2_hidden(sK5(sK0,X1),X1) )
    | spl6_2 ),
    inference(superposition,[],[f51,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f51,plain,
    ( sK1 != k1_tarski(sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl6_2
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f285,plain,
    ( sK0 = sK5(sK0,sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl6_12
  <=> sK0 = sK5(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f1562,plain,
    ( spl6_2
    | spl6_12 ),
    inference(avatar_contradiction_clause,[],[f1561])).

fof(f1561,plain,
    ( $false
    | spl6_2
    | spl6_12 ),
    inference(subsumption_resolution,[],[f1555,f667])).

fof(f667,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),k1_tarski(sK0))
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f286,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f286,plain,
    ( sK0 != sK5(sK0,sK1)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f284])).

fof(f1555,plain,
    ( r2_hidden(sK5(sK0,sK1),k1_tarski(sK0))
    | spl6_2
    | spl6_12 ),
    inference(resolution,[],[f325,f92])).

fof(f92,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f38,f25])).

fof(f25,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f325,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | spl6_2
    | spl6_12 ),
    inference(subsumption_resolution,[],[f324,f286])).

fof(f324,plain,
    ( sK0 = sK5(sK0,sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | spl6_2 ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,
    ( ! [X0] :
        ( sK1 != X0
        | sK0 = sK5(sK0,X0)
        | r2_hidden(sK5(sK0,X0),X0) )
    | spl6_2 ),
    inference(superposition,[],[f51,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1371,plain,
    ( spl6_5
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f1370])).

fof(f1370,plain,
    ( $false
    | spl6_5
    | spl6_6 ),
    inference(subsumption_resolution,[],[f246,f1369])).

fof(f1369,plain,
    ( r2_hidden(sK0,sK2)
    | spl6_5 ),
    inference(subsumption_resolution,[],[f545,f65])).

fof(f65,plain,
    ( k1_xboole_0 != sK2
    | spl6_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f545,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | spl6_5 ),
    inference(superposition,[],[f26,f365])).

fof(f365,plain,
    ( sK0 = sK3(sK2)
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f213,f40])).

fof(f213,plain,
    ( r2_hidden(sK3(sK2),k1_tarski(sK0))
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f72,f93])).

fof(f93,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | r2_hidden(X5,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f37,f25])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f72,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f65,f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f246,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl6_6
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1342,plain,
    ( spl6_3
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f1341])).

fof(f1341,plain,
    ( $false
    | spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f1336,f1185])).

fof(f1185,plain,
    ( r2_hidden(sK5(sK0,sK2),k1_tarski(sK0))
    | spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f1183,f93])).

fof(f1183,plain,
    ( r2_hidden(sK5(sK0,sK2),sK2)
    | spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f1182,f1132])).

fof(f1132,plain,
    ( sK0 != sK5(sK0,sK2)
    | spl6_3
    | ~ spl6_6 ),
    inference(trivial_inequality_removal,[],[f1126])).

fof(f1126,plain,
    ( sK0 != sK5(sK0,sK2)
    | sK2 != sK2
    | spl6_3
    | ~ spl6_6 ),
    inference(resolution,[],[f1016,f247])).

fof(f247,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f245])).

fof(f1016,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | sK0 != sK5(sK0,X1)
        | sK2 != X1 )
    | spl6_3 ),
    inference(inner_rewriting,[],[f1014])).

fof(f1014,plain,
    ( ! [X1] :
        ( sK2 != X1
        | sK0 != sK5(sK0,X1)
        | ~ r2_hidden(sK5(sK0,X1),X1) )
    | spl6_3 ),
    inference(superposition,[],[f56,f36])).

fof(f56,plain,
    ( sK2 != k1_tarski(sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_3
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1182,plain,
    ( sK0 = sK5(sK0,sK2)
    | r2_hidden(sK5(sK0,sK2),sK2)
    | spl6_3 ),
    inference(equality_resolution,[],[f1013])).

fof(f1013,plain,
    ( ! [X0] :
        ( sK2 != X0
        | sK0 = sK5(sK0,X0)
        | r2_hidden(sK5(sK0,X0),X0) )
    | spl6_3 ),
    inference(superposition,[],[f56,f35])).

fof(f1336,plain,
    ( ~ r2_hidden(sK5(sK0,sK2),k1_tarski(sK0))
    | spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f1132,f40])).

fof(f464,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f462,f47])).

fof(f47,plain,
    ( sK1 != sK2
    | spl6_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl6_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f462,plain,
    ( sK1 = sK2
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f55,f50])).

fof(f50,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f55,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f333,plain,
    ( spl6_4
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | spl6_4
    | spl6_7 ),
    inference(subsumption_resolution,[],[f331,f60])).

fof(f60,plain,
    ( k1_xboole_0 != sK1
    | spl6_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f331,plain,
    ( k1_xboole_0 = sK1
    | spl6_4
    | spl6_7 ),
    inference(subsumption_resolution,[],[f328,f250])).

fof(f250,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f249])).

fof(f328,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | spl6_4 ),
    inference(superposition,[],[f26,f222])).

% (25247)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f222,plain,
    ( sK0 = sK3(sK1)
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f204,f40])).

fof(f204,plain,
    ( r2_hidden(sK3(sK1),k1_tarski(sK0))
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f69,f92])).

fof(f69,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f60,f26])).

fof(f252,plain,
    ( spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f233,f249,f245])).

fof(f233,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f91,f42])).

fof(f42,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_tarski(sK0))
      | r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(superposition,[],[f39,f25])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,
    ( ~ spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f22,f49,f63])).

fof(f22,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f23,f58,f54])).

fof(f23,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f43,f49,f45])).

fof(f43,plain,
    ( sK1 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f24])).

fof(f24,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (25243)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.49  % (25251)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.49  % (25251)Refutation not found, incomplete strategy% (25251)------------------------------
% 0.20/0.49  % (25251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25251)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (25251)Memory used [KB]: 10618
% 0.20/0.49  % (25251)Time elapsed: 0.084 s
% 0.20/0.49  % (25251)------------------------------
% 0.20/0.49  % (25251)------------------------------
% 0.20/0.51  % (25238)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (25242)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (25235)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (25239)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (25236)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (25241)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (25263)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (25234)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (25244)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (25259)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (25262)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (25261)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (25255)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (25249)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (25250)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (25237)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (25256)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (25243)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f1572,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f52,f61,f66,f252,f333,f464,f1342,f1371,f1562,f1571])).
% 0.20/0.54  % (25257)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  fof(f1571,plain,(
% 0.20/0.54    spl6_2 | ~spl6_7 | ~spl6_12),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1570])).
% 0.20/0.54  fof(f1570,plain,(
% 0.20/0.54    $false | (spl6_2 | ~spl6_7 | ~spl6_12)),
% 0.20/0.54    inference(subsumption_resolution,[],[f285,f1527])).
% 0.20/0.54  % (25253)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  fof(f1527,plain,(
% 0.20/0.54    sK0 != sK5(sK0,sK1) | (spl6_2 | ~spl6_7)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f1521])).
% 0.20/0.54  fof(f1521,plain,(
% 0.20/0.54    sK0 != sK5(sK0,sK1) | sK1 != sK1 | (spl6_2 | ~spl6_7)),
% 0.20/0.54    inference(resolution,[],[f1402,f251])).
% 0.20/0.54  fof(f251,plain,(
% 0.20/0.54    r2_hidden(sK0,sK1) | ~spl6_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f249])).
% 0.20/0.54  fof(f249,plain,(
% 0.20/0.54    spl6_7 <=> r2_hidden(sK0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.54  fof(f1402,plain,(
% 0.20/0.54    ( ! [X1] : (~r2_hidden(sK0,X1) | sK0 != sK5(sK0,X1) | sK1 != X1) ) | spl6_2),
% 0.20/0.54    inference(inner_rewriting,[],[f1401])).
% 0.20/0.54  fof(f1401,plain,(
% 0.20/0.54    ( ! [X1] : (sK1 != X1 | sK0 != sK5(sK0,X1) | ~r2_hidden(sK5(sK0,X1),X1)) ) | spl6_2),
% 0.20/0.54    inference(superposition,[],[f51,f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X0,X1] : (sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    sK1 != k1_tarski(sK0) | spl6_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    spl6_2 <=> sK1 = k1_tarski(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.54  fof(f285,plain,(
% 0.20/0.54    sK0 = sK5(sK0,sK1) | ~spl6_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f284])).
% 0.20/0.54  fof(f284,plain,(
% 0.20/0.54    spl6_12 <=> sK0 = sK5(sK0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.54  fof(f1562,plain,(
% 0.20/0.54    spl6_2 | spl6_12),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1561])).
% 0.20/0.54  fof(f1561,plain,(
% 0.20/0.54    $false | (spl6_2 | spl6_12)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1555,f667])).
% 0.20/0.54  fof(f667,plain,(
% 0.20/0.54    ~r2_hidden(sK5(sK0,sK1),k1_tarski(sK0)) | spl6_12),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f286,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k1_tarski(X0))) )),
% 0.20/0.54    inference(equality_resolution,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f286,plain,(
% 0.20/0.54    sK0 != sK5(sK0,sK1) | spl6_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f284])).
% 0.20/0.54  fof(f1555,plain,(
% 0.20/0.54    r2_hidden(sK5(sK0,sK1),k1_tarski(sK0)) | (spl6_2 | spl6_12)),
% 0.20/0.54    inference(resolution,[],[f325,f92])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ( ! [X4] : (~r2_hidden(X4,sK1) | r2_hidden(X4,k1_tarski(sK0))) )),
% 0.20/0.54    inference(superposition,[],[f38,f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.54    inference(negated_conjecture,[],[f18])).
% 0.20/0.54  fof(f18,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(equality_resolution,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.54  fof(f325,plain,(
% 0.20/0.54    r2_hidden(sK5(sK0,sK1),sK1) | (spl6_2 | spl6_12)),
% 0.20/0.54    inference(subsumption_resolution,[],[f324,f286])).
% 0.20/0.54  fof(f324,plain,(
% 0.20/0.54    sK0 = sK5(sK0,sK1) | r2_hidden(sK5(sK0,sK1),sK1) | spl6_2),
% 0.20/0.54    inference(equality_resolution,[],[f77])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X0] : (sK1 != X0 | sK0 = sK5(sK0,X0) | r2_hidden(sK5(sK0,X0),X0)) ) | spl6_2),
% 0.20/0.54    inference(superposition,[],[f51,f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X0,X1] : (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f1371,plain,(
% 0.20/0.54    spl6_5 | spl6_6),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1370])).
% 0.20/0.54  fof(f1370,plain,(
% 0.20/0.54    $false | (spl6_5 | spl6_6)),
% 0.20/0.54    inference(subsumption_resolution,[],[f246,f1369])).
% 0.20/0.54  fof(f1369,plain,(
% 0.20/0.54    r2_hidden(sK0,sK2) | spl6_5),
% 0.20/0.54    inference(subsumption_resolution,[],[f545,f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    k1_xboole_0 != sK2 | spl6_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    spl6_5 <=> k1_xboole_0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.54  fof(f545,plain,(
% 0.20/0.54    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | spl6_5),
% 0.20/0.54    inference(superposition,[],[f26,f365])).
% 0.20/0.54  fof(f365,plain,(
% 0.20/0.54    sK0 = sK3(sK2) | spl6_5),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f213,f40])).
% 0.20/0.54  fof(f213,plain,(
% 0.20/0.54    r2_hidden(sK3(sK2),k1_tarski(sK0)) | spl6_5),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f72,f93])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X5] : (~r2_hidden(X5,sK2) | r2_hidden(X5,k1_tarski(sK0))) )),
% 0.20/0.54    inference(superposition,[],[f37,f25])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(equality_resolution,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    r2_hidden(sK3(sK2),sK2) | spl6_5),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f65,f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.54  fof(f246,plain,(
% 0.20/0.54    ~r2_hidden(sK0,sK2) | spl6_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f245])).
% 0.20/0.54  fof(f245,plain,(
% 0.20/0.54    spl6_6 <=> r2_hidden(sK0,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.54  fof(f1342,plain,(
% 0.20/0.54    spl6_3 | ~spl6_6),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1341])).
% 0.20/0.54  fof(f1341,plain,(
% 0.20/0.54    $false | (spl6_3 | ~spl6_6)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1336,f1185])).
% 0.20/0.54  fof(f1185,plain,(
% 0.20/0.54    r2_hidden(sK5(sK0,sK2),k1_tarski(sK0)) | (spl6_3 | ~spl6_6)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f1183,f93])).
% 0.20/0.54  fof(f1183,plain,(
% 0.20/0.54    r2_hidden(sK5(sK0,sK2),sK2) | (spl6_3 | ~spl6_6)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1182,f1132])).
% 0.20/0.54  fof(f1132,plain,(
% 0.20/0.54    sK0 != sK5(sK0,sK2) | (spl6_3 | ~spl6_6)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f1126])).
% 0.20/0.54  fof(f1126,plain,(
% 0.20/0.54    sK0 != sK5(sK0,sK2) | sK2 != sK2 | (spl6_3 | ~spl6_6)),
% 0.20/0.54    inference(resolution,[],[f1016,f247])).
% 0.20/0.54  fof(f247,plain,(
% 0.20/0.54    r2_hidden(sK0,sK2) | ~spl6_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f245])).
% 0.20/0.54  fof(f1016,plain,(
% 0.20/0.54    ( ! [X1] : (~r2_hidden(sK0,X1) | sK0 != sK5(sK0,X1) | sK2 != X1) ) | spl6_3),
% 0.20/0.54    inference(inner_rewriting,[],[f1014])).
% 0.20/0.54  fof(f1014,plain,(
% 0.20/0.54    ( ! [X1] : (sK2 != X1 | sK0 != sK5(sK0,X1) | ~r2_hidden(sK5(sK0,X1),X1)) ) | spl6_3),
% 0.20/0.54    inference(superposition,[],[f56,f36])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    sK2 != k1_tarski(sK0) | spl6_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    spl6_3 <=> sK2 = k1_tarski(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.54  fof(f1182,plain,(
% 0.20/0.54    sK0 = sK5(sK0,sK2) | r2_hidden(sK5(sK0,sK2),sK2) | spl6_3),
% 0.20/0.54    inference(equality_resolution,[],[f1013])).
% 0.20/0.54  fof(f1013,plain,(
% 0.20/0.54    ( ! [X0] : (sK2 != X0 | sK0 = sK5(sK0,X0) | r2_hidden(sK5(sK0,X0),X0)) ) | spl6_3),
% 0.20/0.54    inference(superposition,[],[f56,f35])).
% 0.20/0.54  fof(f1336,plain,(
% 0.20/0.54    ~r2_hidden(sK5(sK0,sK2),k1_tarski(sK0)) | (spl6_3 | ~spl6_6)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f1132,f40])).
% 0.20/0.54  fof(f464,plain,(
% 0.20/0.54    spl6_1 | ~spl6_2 | ~spl6_3),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f463])).
% 0.20/0.54  fof(f463,plain,(
% 0.20/0.54    $false | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.20/0.54    inference(subsumption_resolution,[],[f462,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    sK1 != sK2 | spl6_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    spl6_1 <=> sK1 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.54  fof(f462,plain,(
% 0.20/0.54    sK1 = sK2 | (~spl6_2 | ~spl6_3)),
% 0.20/0.54    inference(forward_demodulation,[],[f55,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    sK1 = k1_tarski(sK0) | ~spl6_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f49])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    sK2 = k1_tarski(sK0) | ~spl6_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f54])).
% 0.20/0.54  fof(f333,plain,(
% 0.20/0.54    spl6_4 | spl6_7),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f332])).
% 0.20/0.54  fof(f332,plain,(
% 0.20/0.54    $false | (spl6_4 | spl6_7)),
% 0.20/0.54    inference(subsumption_resolution,[],[f331,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    k1_xboole_0 != sK1 | spl6_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    spl6_4 <=> k1_xboole_0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.54  fof(f331,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | (spl6_4 | spl6_7)),
% 0.20/0.54    inference(subsumption_resolution,[],[f328,f250])).
% 0.20/0.54  fof(f250,plain,(
% 0.20/0.54    ~r2_hidden(sK0,sK1) | spl6_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f249])).
% 0.20/0.54  fof(f328,plain,(
% 0.20/0.54    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | spl6_4),
% 0.20/0.54    inference(superposition,[],[f26,f222])).
% 0.20/0.54  % (25247)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  fof(f222,plain,(
% 0.20/0.54    sK0 = sK3(sK1) | spl6_4),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f204,f40])).
% 0.20/0.54  fof(f204,plain,(
% 0.20/0.54    r2_hidden(sK3(sK1),k1_tarski(sK0)) | spl6_4),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f69,f92])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    r2_hidden(sK3(sK1),sK1) | spl6_4),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f60,f26])).
% 0.20/0.54  fof(f252,plain,(
% 0.20/0.54    spl6_6 | spl6_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f233,f249,f245])).
% 0.20/0.54  fof(f233,plain,(
% 0.20/0.54    r2_hidden(sK0,sK1) | r2_hidden(sK0,sK2)),
% 0.20/0.54    inference(resolution,[],[f91,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.20/0.54    inference(equality_resolution,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.20/0.54    inference(equality_resolution,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ( ! [X3] : (~r2_hidden(X3,k1_tarski(sK0)) | r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.20/0.54    inference(superposition,[],[f39,f25])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(equality_resolution,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ~spl6_5 | ~spl6_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f22,f49,f63])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ~spl6_3 | ~spl6_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f23,f58,f54])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ~spl6_1 | ~spl6_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f43,f49,f45])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    sK1 != k1_tarski(sK0) | sK1 != sK2),
% 0.20/0.54    inference(inner_rewriting,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (25243)------------------------------
% 0.20/0.54  % (25243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25243)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (25243)Memory used [KB]: 11129
% 0.20/0.54  % (25243)Time elapsed: 0.137 s
% 0.20/0.54  % (25243)------------------------------
% 0.20/0.54  % (25243)------------------------------
% 0.20/0.54  % (25260)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (25258)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (25248)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (25254)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (25233)Success in time 0.191 s
%------------------------------------------------------------------------------
