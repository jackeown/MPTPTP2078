%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t23_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:23 EDT 2019

% Result     : Theorem 9.86s
% Output     : Refutation 9.86s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 134 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  170 ( 337 expanded)
%              Number of equality atoms :   18 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7968,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1437,f7009,f7030,f7032,f7190,f7516,f7967])).

fof(f7967,plain,
    ( ~ spl5_8
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f7966])).

fof(f7966,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f7965,f7838])).

fof(f7838,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f7534,f1374,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t23_xboole_1.p',d3_xboole_0)).

fof(f1374,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl5_8 ),
    inference(resolution,[],[f423,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t23_xboole_1.p',d4_xboole_0)).

fof(f423,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl5_8
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f7534,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f7078,f1373])).

fof(f1373,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f423,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f7078,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_11 ),
    inference(resolution,[],[f426,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f426,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl5_11
  <=> ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f7965,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f7942,f1373])).

fof(f7942,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f1405,f46])).

fof(f1405,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f1371,f25])).

fof(f25,plain,(
    k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t23_xboole_1.p',t23_xboole_1)).

fof(f1371,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_8 ),
    inference(resolution,[],[f423,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f7516,plain,
    ( ~ spl5_12
    | spl5_45 ),
    inference(avatar_contradiction_clause,[],[f7515])).

fof(f7515,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f7489,f7143])).

fof(f7143,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f435,f47])).

fof(f435,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl5_12
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f7489,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_45 ),
    inference(resolution,[],[f7023,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f7023,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f7022])).

fof(f7022,plain,
    ( spl5_45
  <=> ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f7190,plain,
    ( ~ spl5_12
    | spl5_47 ),
    inference(avatar_contradiction_clause,[],[f7189])).

fof(f7189,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_47 ),
    inference(subsumption_resolution,[],[f7158,f7029])).

fof(f7029,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f7028])).

fof(f7028,plain,
    ( spl5_47
  <=> ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f7158,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_12 ),
    inference(resolution,[],[f435,f48])).

fof(f7032,plain,
    ( spl5_10
    | spl5_12
    | spl5_9 ),
    inference(avatar_split_clause,[],[f7031,f419,f434,f428])).

fof(f428,plain,
    ( spl5_10
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f419,plain,
    ( spl5_9
  <=> ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f7031,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f1680,f25])).

fof(f1680,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK2))
    | k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_9 ),
    inference(resolution,[],[f420,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f420,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f419])).

fof(f7030,plain,
    ( ~ spl5_45
    | ~ spl5_47
    | spl5_9 ),
    inference(avatar_split_clause,[],[f1681,f419,f7028,f7022])).

fof(f1681,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl5_9 ),
    inference(resolution,[],[f420,f46])).

fof(f7009,plain,
    ( spl5_9
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f7008])).

fof(f7008,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f6983,f1517])).

fof(f1517,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f429,f47])).

fof(f429,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f428])).

fof(f6983,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(resolution,[],[f1701,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1701,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f1681,f1516])).

fof(f1516,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f429,f48])).

fof(f1437,plain,
    ( ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f1436])).

fof(f1436,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f429,f1407])).

fof(f1407,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f1372,f25])).

fof(f1372,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK2))
    | k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_8 ),
    inference(resolution,[],[f423,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
