%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:51 EST 2020

% Result     : Theorem 2.97s
% Output     : Refutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 297 expanded)
%              Number of leaves         :   16 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  209 ( 764 expanded)
%              Number of equality atoms :   85 ( 294 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1599,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f53,f54,f61,f68,f69,f563,f567,f1390,f1435,f1598])).

fof(f1598,plain,
    ( spl4_5
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f1597])).

fof(f1597,plain,
    ( $false
    | spl4_5
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1596,f67])).

fof(f67,plain,
    ( sK1 != k2_xboole_0(sK1,k1_tarski(sK0))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_5
  <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1596,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f1562,f144])).

fof(f144,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X10,X10)) = X9 ),
    inference(forward_demodulation,[],[f133,f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f133,plain,(
    ! [X10,X9] : k2_xboole_0(X9,X9) = k2_xboole_0(X9,k4_xboole_0(X10,X10)) ),
    inference(superposition,[],[f17,f125])).

fof(f125,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X2) = k4_xboole_0(X3,X3) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X2) = k4_xboole_0(X3,X3)
      | k4_xboole_0(X2,X2) = k4_xboole_0(X3,X3) ) ),
    inference(resolution,[],[f103,f102])).

fof(f102,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK3(X3,X3,k4_xboole_0(X4,X5)),X4)
      | k4_xboole_0(X3,X3) = k4_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f98,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f98,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3
      | r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(resolution,[],[f26,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f103,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK3(X6,X6,k4_xboole_0(X7,X8)),X8)
      | k4_xboole_0(X7,X8) = k4_xboole_0(X6,X6) ) ),
    inference(resolution,[],[f98,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1562,plain,
    ( ! [X54] : k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k4_xboole_0(X54,X54))
    | ~ spl4_9 ),
    inference(superposition,[],[f17,f1396])).

fof(f1396,plain,
    ( ! [X2] : k4_xboole_0(X2,X2) = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_9 ),
    inference(superposition,[],[f1389,f125])).

fof(f1389,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f1387])).

fof(f1387,plain,
    ( spl4_9
  <=> k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(k1_tarski(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1435,plain,
    ( ~ spl4_10
    | spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1421,f1387,f557,f1432])).

fof(f1432,plain,
    ( spl4_10
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f557,plain,
    ( spl4_6
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1421,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl4_6
    | ~ spl4_9 ),
    inference(superposition,[],[f582,f1389])).

fof(f582,plain,
    ( ! [X2] : k1_tarski(sK0) != k4_xboole_0(X2,X2)
    | spl4_6 ),
    inference(superposition,[],[f558,f125])).

fof(f558,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f557])).

fof(f1390,plain,
    ( spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f1384,f42,f1387])).

fof(f42,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1384,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f1373])).

fof(f1373,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(k1_tarski(sK0),sK1))
    | k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f473,f102])).

fof(f473,plain,
    ( ! [X17,X18] :
        ( ~ r2_hidden(sK3(X17,k4_xboole_0(X18,sK1),X17),k1_tarski(sK0))
        | k4_xboole_0(X17,k4_xboole_0(X18,sK1)) = X17 )
    | ~ spl4_2 ),
    inference(resolution,[],[f463,f203])).

fof(f203,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(X5,X6,X5),X6)
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(subsumption_resolution,[],[f201,f25])).

fof(f201,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(X5,X6,X5),X6)
      | ~ r2_hidden(sK3(X5,X6,X5),X5)
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(X5,X6,X5),X6)
      | ~ r2_hidden(sK3(X5,X6,X5),X5)
      | k4_xboole_0(X5,X6) = X5
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(resolution,[],[f24,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f25])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f463,plain,
    ( ! [X10,X9] :
        ( ~ r2_hidden(X10,k4_xboole_0(X9,sK1))
        | ~ r2_hidden(X10,k1_tarski(sK0)) )
    | ~ spl4_2 ),
    inference(superposition,[],[f34,f445])).

fof(f445,plain,
    ( ! [X13] : k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(X13,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f287,f44])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f287,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,X7)
      | k1_tarski(X5) = k4_xboole_0(k1_tarski(X5),k4_xboole_0(X6,X7)) ) ),
    inference(resolution,[],[f204,f34])).

fof(f204,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(subsumption_resolution,[],[f199,f32])).

fof(f32,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X0))
      | r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X0))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_tarski(X0))
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(superposition,[],[f24,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sK3(k1_tarski(X0),X1,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f81,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f567,plain,
    ( spl4_8
    | spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f553,f42,f561,f565])).

fof(f565,plain,
    ( spl4_8
  <=> ! [X1] : k1_tarski(sK0) = k4_xboole_0(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f561,plain,
    ( spl4_7
  <=> ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f553,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK0,k4_xboole_0(X2,sK1))
        | k1_tarski(sK0) = k4_xboole_0(X1,X1) )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f546])).

fof(f546,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK0,k4_xboole_0(X2,sK1))
        | k1_tarski(sK0) = k4_xboole_0(X1,X1)
        | k1_tarski(sK0) = k4_xboole_0(X1,X1) )
    | ~ spl4_2 ),
    inference(superposition,[],[f459,f101])).

fof(f101,plain,(
    ! [X2,X1] :
      ( sK3(X1,X1,k1_tarski(X2)) = X2
      | k1_tarski(X2) = k4_xboole_0(X1,X1) ) ),
    inference(resolution,[],[f98,f30])).

fof(f459,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(X1,X1,k1_tarski(sK0)),k4_xboole_0(X0,sK1))
        | k1_tarski(sK0) = k4_xboole_0(X1,X1) )
    | ~ spl4_2 ),
    inference(superposition,[],[f103,f445])).

fof(f563,plain,
    ( spl4_6
    | spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f554,f42,f561,f557])).

fof(f554,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k4_xboole_0(X0,sK1))
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f545])).

fof(f545,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k4_xboole_0(X0,sK1))
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) )
    | ~ spl4_2 ),
    inference(superposition,[],[f459,f82])).

fof(f69,plain,
    ( ~ spl4_5
    | spl4_4 ),
    inference(avatar_split_clause,[],[f63,f58,f65])).

fof(f58,plain,
    ( spl4_4
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f63,plain,
    ( sK1 != k2_xboole_0(sK1,k1_tarski(sK0))
    | spl4_4 ),
    inference(superposition,[],[f60,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f60,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f68,plain,
    ( ~ spl4_5
    | spl4_4 ),
    inference(avatar_split_clause,[],[f62,f58,f65])).

fof(f62,plain,
    ( sK1 != k2_xboole_0(sK1,k1_tarski(sK0))
    | spl4_4 ),
    inference(superposition,[],[f60,f18])).

fof(f61,plain,
    ( ~ spl4_4
    | spl4_3 ),
    inference(avatar_split_clause,[],[f56,f50,f58])).

fof(f50,plain,
    ( spl4_3
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f56,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | spl4_3 ),
    inference(superposition,[],[f52,f17])).

fof(f52,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f54,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f48,f37,f50])).

fof(f37,plain,
    ( spl4_1
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f48,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl4_1 ),
    inference(superposition,[],[f39,f18])).

fof(f39,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f53,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f47,f37,f50])).

fof(f47,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl4_1 ),
    inference(superposition,[],[f39,f18])).

fof(f45,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f15,f42])).

fof(f15,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f40,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:16:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (9356)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.52  % (9366)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.52  % (9364)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.52  % (9359)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.52  % (9360)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.53  % (9358)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.53  % (9354)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.22/0.53  % (9376)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.22/0.53  % (9377)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.22/0.54  % (9369)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.22/0.54  % (9367)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.33/0.54  % (9368)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.33/0.54  % (9355)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.54  % (9373)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.54  % (9355)Refutation not found, incomplete strategy% (9355)------------------------------
% 1.33/0.54  % (9355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (9383)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.54  % (9374)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.54  % (9379)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.54  % (9382)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.54  % (9378)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.54  % (9365)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.33/0.54  % (9371)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.54  % (9361)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.54  % (9370)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.33/0.55  % (9371)Refutation not found, incomplete strategy% (9371)------------------------------
% 1.33/0.55  % (9371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (9371)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (9371)Memory used [KB]: 1791
% 1.33/0.55  % (9371)Time elapsed: 0.140 s
% 1.33/0.55  % (9371)------------------------------
% 1.33/0.55  % (9371)------------------------------
% 1.33/0.55  % (9370)Refutation not found, incomplete strategy% (9370)------------------------------
% 1.33/0.55  % (9370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (9370)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (9370)Memory used [KB]: 10618
% 1.33/0.55  % (9370)Time elapsed: 0.140 s
% 1.33/0.55  % (9370)------------------------------
% 1.33/0.55  % (9370)------------------------------
% 1.33/0.55  % (9355)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (9355)Memory used [KB]: 1663
% 1.33/0.55  % (9355)Time elapsed: 0.127 s
% 1.33/0.55  % (9355)------------------------------
% 1.33/0.55  % (9355)------------------------------
% 1.33/0.55  % (9368)Refutation not found, incomplete strategy% (9368)------------------------------
% 1.33/0.55  % (9368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (9368)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (9368)Memory used [KB]: 1663
% 1.33/0.55  % (9368)Time elapsed: 0.144 s
% 1.33/0.55  % (9368)------------------------------
% 1.33/0.55  % (9368)------------------------------
% 1.33/0.55  % (9363)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.33/0.55  % (9362)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.55  % (9375)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.33/0.55  % (9381)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.55  % (9383)Refutation not found, incomplete strategy% (9383)------------------------------
% 1.33/0.55  % (9383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (9383)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (9383)Memory used [KB]: 1663
% 1.33/0.55  % (9383)Time elapsed: 0.150 s
% 1.33/0.55  % (9383)------------------------------
% 1.33/0.55  % (9383)------------------------------
% 1.33/0.56  % (9357)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.57  % (9372)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.57  % (9380)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.37/0.70  % (9390)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.37/0.71  % (9388)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.37/0.71  % (9387)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.37/0.71  % (9389)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.37/0.74  % (9391)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.37/0.74  % (9357)Refutation not found, incomplete strategy% (9357)------------------------------
% 2.37/0.74  % (9357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.37/0.74  % (9357)Termination reason: Refutation not found, incomplete strategy
% 2.37/0.74  
% 2.37/0.74  % (9357)Memory used [KB]: 6140
% 2.37/0.74  % (9357)Time elapsed: 0.288 s
% 2.37/0.74  % (9357)------------------------------
% 2.37/0.74  % (9357)------------------------------
% 2.37/0.74  % (9391)Refutation not found, incomplete strategy% (9391)------------------------------
% 2.37/0.74  % (9391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.37/0.74  % (9391)Termination reason: Refutation not found, incomplete strategy
% 2.37/0.74  
% 2.37/0.74  % (9391)Memory used [KB]: 10618
% 2.37/0.74  % (9391)Time elapsed: 0.156 s
% 2.37/0.74  % (9391)------------------------------
% 2.37/0.74  % (9391)------------------------------
% 2.97/0.79  % (9354)Refutation found. Thanks to Tanya!
% 2.97/0.79  % SZS status Theorem for theBenchmark
% 2.97/0.79  % SZS output start Proof for theBenchmark
% 2.97/0.79  fof(f1599,plain,(
% 2.97/0.79    $false),
% 2.97/0.79    inference(avatar_sat_refutation,[],[f40,f45,f53,f54,f61,f68,f69,f563,f567,f1390,f1435,f1598])).
% 2.97/0.79  fof(f1598,plain,(
% 2.97/0.79    spl4_5 | ~spl4_9),
% 2.97/0.79    inference(avatar_contradiction_clause,[],[f1597])).
% 2.97/0.79  fof(f1597,plain,(
% 2.97/0.79    $false | (spl4_5 | ~spl4_9)),
% 2.97/0.79    inference(subsumption_resolution,[],[f1596,f67])).
% 2.97/0.79  fof(f67,plain,(
% 2.97/0.79    sK1 != k2_xboole_0(sK1,k1_tarski(sK0)) | spl4_5),
% 2.97/0.79    inference(avatar_component_clause,[],[f65])).
% 2.97/0.79  fof(f65,plain,(
% 2.97/0.79    spl4_5 <=> sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 2.97/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.97/0.79  fof(f1596,plain,(
% 2.97/0.79    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_9),
% 2.97/0.79    inference(forward_demodulation,[],[f1562,f144])).
% 2.97/0.79  fof(f144,plain,(
% 2.97/0.79    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X10,X10)) = X9) )),
% 2.97/0.79    inference(forward_demodulation,[],[f133,f19])).
% 2.97/0.79  fof(f19,plain,(
% 2.97/0.79    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.97/0.79    inference(cnf_transformation,[],[f13])).
% 2.97/0.79  fof(f13,plain,(
% 2.97/0.79    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.97/0.79    inference(rectify,[],[f3])).
% 2.97/0.79  fof(f3,axiom,(
% 2.97/0.79    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.97/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.97/0.79  fof(f133,plain,(
% 2.97/0.79    ( ! [X10,X9] : (k2_xboole_0(X9,X9) = k2_xboole_0(X9,k4_xboole_0(X10,X10))) )),
% 2.97/0.79    inference(superposition,[],[f17,f125])).
% 2.97/0.79  fof(f125,plain,(
% 2.97/0.79    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = k4_xboole_0(X3,X3)) )),
% 2.97/0.79    inference(duplicate_literal_removal,[],[f123])).
% 2.97/0.79  fof(f123,plain,(
% 2.97/0.79    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = k4_xboole_0(X3,X3) | k4_xboole_0(X2,X2) = k4_xboole_0(X3,X3)) )),
% 2.97/0.79    inference(resolution,[],[f103,f102])).
% 2.97/0.79  fof(f102,plain,(
% 2.97/0.79    ( ! [X4,X5,X3] : (r2_hidden(sK3(X3,X3,k4_xboole_0(X4,X5)),X4) | k4_xboole_0(X3,X3) = k4_xboole_0(X4,X5)) )),
% 2.97/0.79    inference(resolution,[],[f98,f35])).
% 2.97/0.79  fof(f35,plain,(
% 2.97/0.79    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 2.97/0.79    inference(equality_resolution,[],[f27])).
% 2.97/0.79  fof(f27,plain,(
% 2.97/0.79    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.97/0.79    inference(cnf_transformation,[],[f2])).
% 2.97/0.79  fof(f2,axiom,(
% 2.97/0.79    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.97/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.97/0.79  fof(f98,plain,(
% 2.97/0.79    ( ! [X2,X3] : (r2_hidden(sK3(X2,X2,X3),X3) | k4_xboole_0(X2,X2) = X3) )),
% 2.97/0.79    inference(duplicate_literal_removal,[],[f92])).
% 2.97/0.79  fof(f92,plain,(
% 2.97/0.79    ( ! [X2,X3] : (r2_hidden(sK3(X2,X2,X3),X3) | k4_xboole_0(X2,X2) = X3 | r2_hidden(sK3(X2,X2,X3),X3) | k4_xboole_0(X2,X2) = X3) )),
% 2.97/0.79    inference(resolution,[],[f26,f25])).
% 2.97/0.79  fof(f25,plain,(
% 2.97/0.79    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.97/0.79    inference(cnf_transformation,[],[f2])).
% 2.97/0.79  fof(f26,plain,(
% 2.97/0.79    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.97/0.79    inference(cnf_transformation,[],[f2])).
% 2.97/0.79  fof(f103,plain,(
% 2.97/0.79    ( ! [X6,X8,X7] : (~r2_hidden(sK3(X6,X6,k4_xboole_0(X7,X8)),X8) | k4_xboole_0(X7,X8) = k4_xboole_0(X6,X6)) )),
% 2.97/0.79    inference(resolution,[],[f98,f34])).
% 2.97/0.79  fof(f34,plain,(
% 2.97/0.79    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 2.97/0.79    inference(equality_resolution,[],[f28])).
% 2.97/0.79  fof(f28,plain,(
% 2.97/0.79    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.97/0.79    inference(cnf_transformation,[],[f2])).
% 2.97/0.79  fof(f17,plain,(
% 2.97/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.97/0.79    inference(cnf_transformation,[],[f5])).
% 2.97/0.79  fof(f5,axiom,(
% 2.97/0.79    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.97/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.97/0.79  fof(f1562,plain,(
% 2.97/0.79    ( ! [X54] : (k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k4_xboole_0(X54,X54))) ) | ~spl4_9),
% 2.97/0.79    inference(superposition,[],[f17,f1396])).
% 2.97/0.79  fof(f1396,plain,(
% 2.97/0.79    ( ! [X2] : (k4_xboole_0(X2,X2) = k4_xboole_0(k1_tarski(sK0),sK1)) ) | ~spl4_9),
% 2.97/0.79    inference(superposition,[],[f1389,f125])).
% 2.97/0.79  fof(f1389,plain,(
% 2.97/0.79    k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(k1_tarski(sK0),sK1)) | ~spl4_9),
% 2.97/0.79    inference(avatar_component_clause,[],[f1387])).
% 2.97/0.79  fof(f1387,plain,(
% 2.97/0.79    spl4_9 <=> k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(k1_tarski(sK0),sK1))),
% 2.97/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.97/0.79  fof(f1435,plain,(
% 2.97/0.79    ~spl4_10 | spl4_6 | ~spl4_9),
% 2.97/0.79    inference(avatar_split_clause,[],[f1421,f1387,f557,f1432])).
% 2.97/0.79  fof(f1432,plain,(
% 2.97/0.79    spl4_10 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 2.97/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.97/0.79  fof(f557,plain,(
% 2.97/0.79    spl4_6 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 2.97/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.97/0.79  fof(f1421,plain,(
% 2.97/0.79    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | (spl4_6 | ~spl4_9)),
% 2.97/0.79    inference(superposition,[],[f582,f1389])).
% 2.97/0.79  fof(f582,plain,(
% 2.97/0.79    ( ! [X2] : (k1_tarski(sK0) != k4_xboole_0(X2,X2)) ) | spl4_6),
% 2.97/0.79    inference(superposition,[],[f558,f125])).
% 2.97/0.79  fof(f558,plain,(
% 2.97/0.79    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | spl4_6),
% 2.97/0.79    inference(avatar_component_clause,[],[f557])).
% 2.97/0.79  fof(f1390,plain,(
% 2.97/0.79    spl4_9 | ~spl4_2),
% 2.97/0.79    inference(avatar_split_clause,[],[f1384,f42,f1387])).
% 2.97/0.79  fof(f42,plain,(
% 2.97/0.79    spl4_2 <=> r2_hidden(sK0,sK1)),
% 2.97/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.97/0.79  fof(f1384,plain,(
% 2.97/0.79    k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(k1_tarski(sK0),sK1)) | ~spl4_2),
% 2.97/0.79    inference(duplicate_literal_removal,[],[f1373])).
% 2.97/0.79  fof(f1373,plain,(
% 2.97/0.79    k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(k1_tarski(sK0),sK1)) | k4_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(k1_tarski(sK0),sK1)) | ~spl4_2),
% 2.97/0.79    inference(resolution,[],[f473,f102])).
% 2.97/0.79  fof(f473,plain,(
% 2.97/0.79    ( ! [X17,X18] : (~r2_hidden(sK3(X17,k4_xboole_0(X18,sK1),X17),k1_tarski(sK0)) | k4_xboole_0(X17,k4_xboole_0(X18,sK1)) = X17) ) | ~spl4_2),
% 2.97/0.79    inference(resolution,[],[f463,f203])).
% 2.97/0.79  fof(f203,plain,(
% 2.97/0.79    ( ! [X6,X5] : (r2_hidden(sK3(X5,X6,X5),X6) | k4_xboole_0(X5,X6) = X5) )),
% 2.97/0.79    inference(subsumption_resolution,[],[f201,f25])).
% 2.97/0.79  fof(f201,plain,(
% 2.97/0.79    ( ! [X6,X5] : (r2_hidden(sK3(X5,X6,X5),X6) | ~r2_hidden(sK3(X5,X6,X5),X5) | k4_xboole_0(X5,X6) = X5) )),
% 2.97/0.79    inference(duplicate_literal_removal,[],[f193])).
% 2.97/0.79  fof(f193,plain,(
% 2.97/0.79    ( ! [X6,X5] : (r2_hidden(sK3(X5,X6,X5),X6) | ~r2_hidden(sK3(X5,X6,X5),X5) | k4_xboole_0(X5,X6) = X5 | k4_xboole_0(X5,X6) = X5) )),
% 2.97/0.79    inference(resolution,[],[f24,f81])).
% 2.97/0.79  fof(f81,plain,(
% 2.97/0.79    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 2.97/0.79    inference(factoring,[],[f25])).
% 2.97/0.79  fof(f24,plain,(
% 2.97/0.79    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.97/0.79    inference(cnf_transformation,[],[f2])).
% 2.97/0.79  fof(f463,plain,(
% 2.97/0.79    ( ! [X10,X9] : (~r2_hidden(X10,k4_xboole_0(X9,sK1)) | ~r2_hidden(X10,k1_tarski(sK0))) ) | ~spl4_2),
% 2.97/0.79    inference(superposition,[],[f34,f445])).
% 2.97/0.79  fof(f445,plain,(
% 2.97/0.79    ( ! [X13] : (k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(X13,sK1))) ) | ~spl4_2),
% 2.97/0.79    inference(resolution,[],[f287,f44])).
% 2.97/0.79  fof(f44,plain,(
% 2.97/0.79    r2_hidden(sK0,sK1) | ~spl4_2),
% 2.97/0.79    inference(avatar_component_clause,[],[f42])).
% 2.97/0.79  fof(f287,plain,(
% 2.97/0.79    ( ! [X6,X7,X5] : (~r2_hidden(X5,X7) | k1_tarski(X5) = k4_xboole_0(k1_tarski(X5),k4_xboole_0(X6,X7))) )),
% 2.97/0.79    inference(resolution,[],[f204,f34])).
% 2.97/0.79  fof(f204,plain,(
% 2.97/0.79    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 2.97/0.79    inference(subsumption_resolution,[],[f199,f32])).
% 2.97/0.79  fof(f32,plain,(
% 2.97/0.79    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 2.97/0.79    inference(equality_resolution,[],[f31])).
% 2.97/0.79  fof(f31,plain,(
% 2.97/0.79    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 2.97/0.79    inference(equality_resolution,[],[f20])).
% 2.97/0.79  fof(f20,plain,(
% 2.97/0.79    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.97/0.79    inference(cnf_transformation,[],[f7])).
% 2.97/0.79  fof(f7,axiom,(
% 2.97/0.79    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.97/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.97/0.79  fof(f199,plain,(
% 2.97/0.79    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X0)) | r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 2.97/0.79    inference(duplicate_literal_removal,[],[f196])).
% 2.97/0.79  fof(f196,plain,(
% 2.97/0.79    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X0)) | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_tarski(X0)) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 2.97/0.79    inference(superposition,[],[f24,f82])).
% 2.97/0.79  fof(f82,plain,(
% 2.97/0.79    ( ! [X0,X1] : (sK3(k1_tarski(X0),X1,k1_tarski(X0)) = X0 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 2.97/0.79    inference(resolution,[],[f81,f30])).
% 2.97/0.79  fof(f30,plain,(
% 2.97/0.79    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 2.97/0.79    inference(equality_resolution,[],[f21])).
% 2.97/0.79  fof(f21,plain,(
% 2.97/0.79    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.97/0.79    inference(cnf_transformation,[],[f7])).
% 2.97/0.79  fof(f567,plain,(
% 2.97/0.79    spl4_8 | spl4_7 | ~spl4_2),
% 2.97/0.79    inference(avatar_split_clause,[],[f553,f42,f561,f565])).
% 2.97/0.79  fof(f565,plain,(
% 2.97/0.79    spl4_8 <=> ! [X1] : k1_tarski(sK0) = k4_xboole_0(X1,X1)),
% 2.97/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.97/0.79  fof(f561,plain,(
% 2.97/0.79    spl4_7 <=> ! [X0] : ~r2_hidden(sK0,k4_xboole_0(X0,sK1))),
% 2.97/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.97/0.79  fof(f553,plain,(
% 2.97/0.79    ( ! [X2,X1] : (~r2_hidden(sK0,k4_xboole_0(X2,sK1)) | k1_tarski(sK0) = k4_xboole_0(X1,X1)) ) | ~spl4_2),
% 2.97/0.79    inference(duplicate_literal_removal,[],[f546])).
% 2.97/0.79  fof(f546,plain,(
% 2.97/0.79    ( ! [X2,X1] : (~r2_hidden(sK0,k4_xboole_0(X2,sK1)) | k1_tarski(sK0) = k4_xboole_0(X1,X1) | k1_tarski(sK0) = k4_xboole_0(X1,X1)) ) | ~spl4_2),
% 2.97/0.79    inference(superposition,[],[f459,f101])).
% 2.97/0.79  fof(f101,plain,(
% 2.97/0.79    ( ! [X2,X1] : (sK3(X1,X1,k1_tarski(X2)) = X2 | k1_tarski(X2) = k4_xboole_0(X1,X1)) )),
% 2.97/0.79    inference(resolution,[],[f98,f30])).
% 2.97/0.79  fof(f459,plain,(
% 2.97/0.79    ( ! [X0,X1] : (~r2_hidden(sK3(X1,X1,k1_tarski(sK0)),k4_xboole_0(X0,sK1)) | k1_tarski(sK0) = k4_xboole_0(X1,X1)) ) | ~spl4_2),
% 2.97/0.79    inference(superposition,[],[f103,f445])).
% 2.97/0.79  fof(f563,plain,(
% 2.97/0.79    spl4_6 | spl4_7 | ~spl4_2),
% 2.97/0.79    inference(avatar_split_clause,[],[f554,f42,f561,f557])).
% 2.97/0.79  fof(f554,plain,(
% 2.97/0.79    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,sK1)) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ) | ~spl4_2),
% 2.97/0.79    inference(duplicate_literal_removal,[],[f545])).
% 2.97/0.79  fof(f545,plain,(
% 2.97/0.79    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,sK1)) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ) | ~spl4_2),
% 2.97/0.79    inference(superposition,[],[f459,f82])).
% 2.97/0.79  fof(f69,plain,(
% 2.97/0.79    ~spl4_5 | spl4_4),
% 2.97/0.79    inference(avatar_split_clause,[],[f63,f58,f65])).
% 2.97/0.79  fof(f58,plain,(
% 2.97/0.79    spl4_4 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 2.97/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.97/0.79  fof(f63,plain,(
% 2.97/0.79    sK1 != k2_xboole_0(sK1,k1_tarski(sK0)) | spl4_4),
% 2.97/0.79    inference(superposition,[],[f60,f18])).
% 2.97/0.79  fof(f18,plain,(
% 2.97/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.97/0.79    inference(cnf_transformation,[],[f1])).
% 2.97/0.79  fof(f1,axiom,(
% 2.97/0.79    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.97/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.97/0.79  fof(f60,plain,(
% 2.97/0.79    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | spl4_4),
% 2.97/0.79    inference(avatar_component_clause,[],[f58])).
% 2.97/0.79  fof(f68,plain,(
% 2.97/0.79    ~spl4_5 | spl4_4),
% 2.97/0.79    inference(avatar_split_clause,[],[f62,f58,f65])).
% 2.97/0.79  fof(f62,plain,(
% 2.97/0.79    sK1 != k2_xboole_0(sK1,k1_tarski(sK0)) | spl4_4),
% 2.97/0.79    inference(superposition,[],[f60,f18])).
% 2.97/0.79  fof(f61,plain,(
% 2.97/0.79    ~spl4_4 | spl4_3),
% 2.97/0.79    inference(avatar_split_clause,[],[f56,f50,f58])).
% 2.97/0.79  fof(f50,plain,(
% 2.97/0.79    spl4_3 <=> sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 2.97/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.97/0.79  fof(f56,plain,(
% 2.97/0.79    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | spl4_3),
% 2.97/0.79    inference(superposition,[],[f52,f17])).
% 2.97/0.79  fof(f52,plain,(
% 2.97/0.79    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl4_3),
% 2.97/0.79    inference(avatar_component_clause,[],[f50])).
% 2.97/0.79  fof(f54,plain,(
% 2.97/0.79    ~spl4_3 | spl4_1),
% 2.97/0.79    inference(avatar_split_clause,[],[f48,f37,f50])).
% 2.97/0.79  fof(f37,plain,(
% 2.97/0.79    spl4_1 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.97/0.79    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.97/0.79  fof(f48,plain,(
% 2.97/0.79    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl4_1),
% 2.97/0.79    inference(superposition,[],[f39,f18])).
% 2.97/0.79  fof(f39,plain,(
% 2.97/0.79    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl4_1),
% 2.97/0.79    inference(avatar_component_clause,[],[f37])).
% 2.97/0.79  fof(f53,plain,(
% 2.97/0.79    ~spl4_3 | spl4_1),
% 2.97/0.79    inference(avatar_split_clause,[],[f47,f37,f50])).
% 2.97/0.79  fof(f47,plain,(
% 2.97/0.79    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl4_1),
% 2.97/0.79    inference(superposition,[],[f39,f18])).
% 2.97/0.79  fof(f45,plain,(
% 2.97/0.79    spl4_2),
% 2.97/0.79    inference(avatar_split_clause,[],[f15,f42])).
% 2.97/0.79  fof(f15,plain,(
% 2.97/0.79    r2_hidden(sK0,sK1)),
% 2.97/0.79    inference(cnf_transformation,[],[f14])).
% 2.97/0.79  fof(f14,plain,(
% 2.97/0.79    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 2.97/0.79    inference(ennf_transformation,[],[f12])).
% 2.97/0.79  fof(f12,negated_conjecture,(
% 2.97/0.79    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 2.97/0.79    inference(negated_conjecture,[],[f11])).
% 2.97/0.79  fof(f11,conjecture,(
% 2.97/0.79    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 2.97/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 2.97/0.79  fof(f40,plain,(
% 2.97/0.79    ~spl4_1),
% 2.97/0.79    inference(avatar_split_clause,[],[f16,f37])).
% 2.97/0.79  fof(f16,plain,(
% 2.97/0.79    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.97/0.79    inference(cnf_transformation,[],[f14])).
% 2.97/0.79  % SZS output end Proof for theBenchmark
% 2.97/0.79  % (9354)------------------------------
% 2.97/0.79  % (9354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.97/0.79  % (9354)Termination reason: Refutation
% 2.97/0.79  
% 2.97/0.79  % (9354)Memory used [KB]: 2430
% 2.97/0.79  % (9354)Time elapsed: 0.381 s
% 2.97/0.79  % (9354)------------------------------
% 2.97/0.79  % (9354)------------------------------
% 2.97/0.79  % (9353)Success in time 0.419 s
%------------------------------------------------------------------------------
