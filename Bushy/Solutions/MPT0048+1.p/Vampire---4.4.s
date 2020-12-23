%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t41_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
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

% Result     : Theorem 9.95s
% Output     : Refutation 9.95s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 107 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  148 ( 260 expanded)
%              Number of equality atoms :   17 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f259,f302,f356,f529,f531,f533])).

fof(f533,plain,
    ( ~ spl5_0
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f532])).

fof(f532,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f265,f507])).

fof(f507,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_0 ),
    inference(resolution,[],[f327,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t41_xboole_1.p',d3_xboole_0)).

fof(f327,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f106,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/xboole_1__t41_xboole_1.p',d5_xboole_0)).

fof(f106,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_0
  <=> r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f265,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl5_4
  <=> r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f531,plain,
    ( spl5_4
    | ~ spl5_3
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f530,f105,f108,f264])).

fof(f108,plain,
    ( spl5_3
  <=> ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f530,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_0 ),
    inference(subsumption_resolution,[],[f335,f26])).

fof(f26,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t41_xboole_1.p',t41_xboole_1)).

fof(f335,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_0 ),
    inference(resolution,[],[f106,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f529,plain,
    ( ~ spl5_0
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f506,f295])).

fof(f295,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f506,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_0 ),
    inference(resolution,[],[f327,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f356,plain,
    ( ~ spl5_0
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f336,f301])).

fof(f301,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl5_9
  <=> ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f336,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_0 ),
    inference(resolution,[],[f106,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f302,plain,
    ( spl5_6
    | ~ spl5_9
    | spl5_3 ),
    inference(avatar_split_clause,[],[f274,f108,f300,f294])).

fof(f274,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f109,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f109,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f259,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f229,f201])).

fof(f201,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f114,f103,f45])).

fof(f103,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_1
  <=> ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f114,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f112,f47])).

fof(f112,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_2
  <=> r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f229,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f115,f200,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f200,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f26,f103,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f115,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f112,f46])).

fof(f113,plain,
    ( spl5_0
    | spl5_2 ),
    inference(avatar_split_clause,[],[f100,f111,f105])).

fof(f100,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X1] :
      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X1
      | r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK3(k4_xboole_0(sK0,sK1),sK2,X1),X1) ) ),
    inference(superposition,[],[f26,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
