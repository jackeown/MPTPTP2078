%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t42_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:26 EDT 2019

% Result     : Theorem 9.83s
% Output     : Refutation 9.83s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 143 expanded)
%              Number of leaves         :   13 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  199 ( 360 expanded)
%              Number of equality atoms :   18 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6920,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f656,f4865,f4867,f6425,f6427,f6431,f6434,f6913,f6919])).

fof(f6919,plain,
    ( ~ spl5_14
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f6918])).

fof(f6918,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f649,f6644])).

fof(f6644,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f428,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t42_xboole_1.p',d5_xboole_0)).

fof(f428,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f427])).

fof(f427,plain,
    ( spl5_14
  <=> r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f649,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f648])).

fof(f648,plain,
    ( spl5_28
  <=> r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f6913,plain,
    ( ~ spl5_14
    | spl5_19
    | spl5_29
    | spl5_31 ),
    inference(avatar_contradiction_clause,[],[f6912])).

fof(f6912,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_19
    | ~ spl5_29
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f6911,f767])).

fof(f767,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f428,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f6911,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1))
    | ~ spl5_19
    | ~ spl5_29
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f6884,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t42_xboole_1.p',commutativity_k2_xboole_0)).

fof(f6884,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK1,sK0))
    | ~ spl5_19
    | ~ spl5_29
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f655,f709,f47])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t42_xboole_1.p',d3_xboole_0)).

fof(f709,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0)
    | ~ spl5_19
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f689,f646])).

fof(f646,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f645])).

fof(f645,plain,
    ( spl5_29
  <=> ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f689,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0)
    | r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl5_19 ),
    inference(resolution,[],[f437,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f437,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl5_19
  <=> ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f655,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl5_31
  <=> ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f6434,plain,
    ( spl5_15
    | ~ spl5_18
    | spl5_29 ),
    inference(avatar_contradiction_clause,[],[f6433])).

fof(f6433,plain,
    ( $false
    | ~ spl5_15
    | ~ spl5_18
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f1830,f6388])).

fof(f6388,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0)
    | ~ spl5_15
    | ~ spl5_29 ),
    inference(resolution,[],[f1894,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1894,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f1875,f646])).

fof(f1875,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl5_15 ),
    inference(resolution,[],[f425,f48])).

fof(f425,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl5_15
  <=> ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f1830,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0)
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f440,f50])).

fof(f440,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl5_18
  <=> r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f6431,plain,
    ( ~ spl5_18
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f6430])).

fof(f6430,plain,
    ( $false
    | ~ spl5_18
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f1831,f649])).

fof(f1831,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f440,f49])).

fof(f6427,plain,
    ( spl5_16
    | spl5_18
    | spl5_15 ),
    inference(avatar_split_clause,[],[f6426,f424,f439,f433])).

fof(f433,plain,
    ( spl5_16
  <=> r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f6426,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2))
    | r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f5375,f26])).

fof(f26,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t42_xboole_1.p',t42_xboole_1)).

fof(f5375,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2))
    | r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)
    | ~ spl5_15 ),
    inference(resolution,[],[f425,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f6425,plain,
    ( spl5_15
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f6424])).

fof(f6424,plain,
    ( $false
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f1790,f6417])).

fof(f6417,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f5376,f4372])).

fof(f4372,plain,
    ( ! [X0] : r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(X0,sK1))
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f1789,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1789,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1)
    | ~ spl5_16 ),
    inference(resolution,[],[f434,f50])).

fof(f434,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f433])).

fof(f5376,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl5_15 ),
    inference(resolution,[],[f425,f48])).

fof(f1790,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl5_16 ),
    inference(resolution,[],[f434,f49])).

fof(f4867,plain,
    ( ~ spl5_14
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f4866])).

fof(f4866,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f766,f434])).

fof(f766,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f26,f428,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4865,plain,
    ( ~ spl5_14
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f4864])).

fof(f4864,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f765,f440])).

fof(f765,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f26,f428,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f656,plain,
    ( spl5_28
    | ~ spl5_31
    | spl5_17 ),
    inference(avatar_split_clause,[],[f625,f430,f654,f648])).

fof(f430,plain,
    ( spl5_17
  <=> ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f625,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1)
    | r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl5_17 ),
    inference(resolution,[],[f431,f48])).

fof(f431,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f430])).
%------------------------------------------------------------------------------
