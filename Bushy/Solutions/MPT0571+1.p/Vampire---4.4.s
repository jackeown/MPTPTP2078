%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t175_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:54 EDT 2019

% Result     : Theorem 20.90s
% Output     : Refutation 20.90s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 198 expanded)
%              Number of leaves         :    9 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  212 ( 542 expanded)
%              Number of equality atoms :   17 (  98 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f272,f288,f4432,f4452,f4532])).

fof(f4532,plain,
    ( spl11_13
    | ~ spl11_14 ),
    inference(avatar_contradiction_clause,[],[f4531])).

fof(f4531,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f4521,f268])).

fof(f268,plain,
    ( r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl11_14
  <=> r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f4521,plain,
    ( ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl11_13 ),
    inference(resolution,[],[f265,f497])).

fof(f497,plain,(
    ! [X12,X10,X11] :
      ( r2_hidden(X10,k10_relat_1(sK2,k2_xboole_0(X11,X12)))
      | ~ r2_hidden(X10,k10_relat_1(sK2,X11)) ) ),
    inference(duplicate_literal_removal,[],[f489])).

fof(f489,plain,(
    ! [X12,X10,X11] :
      ( ~ r2_hidden(X10,k10_relat_1(sK2,X11))
      | r2_hidden(X10,k10_relat_1(sK2,k2_xboole_0(X11,X12)))
      | ~ r2_hidden(X10,k10_relat_1(sK2,X11)) ) ),
    inference(resolution,[],[f143,f117])).

fof(f117,plain,(
    ! [X23,X21,X22] :
      ( r2_hidden(sK4(sK2,X22,X21),k2_xboole_0(X22,X23))
      | ~ r2_hidden(X21,k10_relat_1(sK2,X22)) ) ),
    inference(resolution,[],[f107,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t175_relat_1.p',d3_xboole_0)).

fof(f107,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK4(sK2,X9,X10),X9)
      | ~ r2_hidden(X10,k10_relat_1(sK2,X9)) ) ),
    inference(resolution,[],[f41,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t175_relat_1.p',d14_relat_1)).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != k10_relat_1(X2,k2_xboole_0(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t175_relat_1.p',t175_relat_1)).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(sK2,X1,X0),X2)
      | ~ r2_hidden(X0,k10_relat_1(sK2,X1))
      | r2_hidden(X0,k10_relat_1(sK2,X2)) ) ),
    inference(subsumption_resolution,[],[f130,f41])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK4(sK2,X1,X0),X2)
      | r2_hidden(X0,k10_relat_1(sK2,X2)) ) ),
    inference(resolution,[],[f106,f76])).

fof(f76,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f106,plain,(
    ! [X8,X7] :
      ( r2_hidden(k4_tarski(X7,sK4(sK2,X8,X7)),sK2)
      | ~ r2_hidden(X7,k10_relat_1(sK2,X8)) ) ),
    inference(resolution,[],[f41,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f265,plain,
    ( ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl11_13
  <=> ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f4452,plain,
    ( spl11_13
    | spl11_15 ),
    inference(avatar_contradiction_clause,[],[f4451])).

fof(f4451,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f265,f4445])).

fof(f4445,plain,
    ( r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f4444,f498])).

fof(f498,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(X7,k10_relat_1(sK2,k2_xboole_0(X9,X8)))
      | ~ r2_hidden(X7,k10_relat_1(sK2,X8)) ) ),
    inference(duplicate_literal_removal,[],[f488])).

fof(f488,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,k10_relat_1(sK2,X8))
      | r2_hidden(X7,k10_relat_1(sK2,k2_xboole_0(X9,X8)))
      | ~ r2_hidden(X7,k10_relat_1(sK2,X8)) ) ),
    inference(resolution,[],[f143,f116])).

fof(f116,plain,(
    ! [X19,X20,X18] :
      ( r2_hidden(sK4(sK2,X19,X18),k2_xboole_0(X20,X19))
      | ~ r2_hidden(X18,k10_relat_1(sK2,X19)) ) ),
    inference(resolution,[],[f107,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4444,plain,
    ( r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1))
    | r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f1351,f271])).

fof(f271,plain,
    ( ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl11_15
  <=> ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f1351,plain,
    ( r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))
    | r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1))
    | r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f196,f100])).

fof(f100,plain,(
    ! [X0] : sQ10_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f86])).

fof(f86,plain,(
    ! [X1,X0] :
      ( sQ10_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).

fof(f196,plain,(
    ! [X2] :
      ( ~ sQ10_eqProxy(X2,k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
      | r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),X2),k10_relat_1(sK2,sK0))
      | r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),X2),k10_relat_1(sK2,sK1))
      | r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),X2),X2) ) ),
    inference(resolution,[],[f129,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X0)
      | r2_hidden(sK8(X0,X1,X2),X1)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | sQ10_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f71,f86])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X0)
      | r2_hidden(sK8(X0,X1,X2),X1)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f129,plain,(
    ! [X0] :
      ( ~ sQ10_eqProxy(k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),X0)
      | ~ sQ10_eqProxy(X0,k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) ) ),
    inference(resolution,[],[f87,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ10_eqProxy(X0,X1)
      | ~ sQ10_eqProxy(X1,X2)
      | sQ10_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f86])).

fof(f87,plain,(
    ~ sQ10_eqProxy(k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f42,f86])).

fof(f42,plain,(
    k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f4432,plain,
    ( ~ spl11_12
    | spl11_15
    | spl11_17 ),
    inference(avatar_contradiction_clause,[],[f4431])).

fof(f4431,plain,
    ( $false
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f4430,f262])).

fof(f262,plain,
    ( r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl11_12
  <=> r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f4430,plain,
    ( ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f4421,f1262])).

fof(f1262,plain,
    ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))),sK0)
    | ~ spl11_12
    | ~ spl11_15 ),
    inference(resolution,[],[f322,f297])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),X0),sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f292,f41])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),X0),sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl11_15 ),
    inference(resolution,[],[f271,f76])).

fof(f322,plain,
    ( r2_hidden(k4_tarski(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),sK4(sK2,k2_xboole_0(sK0,sK1),sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))))),sK2)
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f309,f41])).

fof(f309,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),sK4(sK2,k2_xboole_0(sK0,sK1),sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))))),sK2)
    | ~ spl11_12 ),
    inference(resolution,[],[f262,f78])).

fof(f4421,plain,
    ( r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))),sK0)
    | ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | ~ spl11_12
    | ~ spl11_17 ),
    inference(resolution,[],[f1261,f122])).

fof(f122,plain,(
    ! [X37,X38,X36] :
      ( r2_hidden(sK4(sK2,k2_xboole_0(X37,X38),X36),X38)
      | r2_hidden(sK4(sK2,k2_xboole_0(X37,X38),X36),X37)
      | ~ r2_hidden(X36,k10_relat_1(sK2,k2_xboole_0(X37,X38))) ) ),
    inference(resolution,[],[f107,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1261,plain,
    ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))),sK1)
    | ~ spl11_12
    | ~ spl11_17 ),
    inference(resolution,[],[f322,f304])).

fof(f304,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),X0),sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f299,f41])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),X0),sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl11_17 ),
    inference(resolution,[],[f287,f76])).

fof(f287,plain,
    ( ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl11_17
  <=> ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f288,plain,
    ( ~ spl11_13
    | ~ spl11_17 ),
    inference(avatar_split_clause,[],[f124,f286,f264])).

fof(f124,plain,
    ( ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f87,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(sK8(X0,X1,X2),X2)
      | sQ10_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f70,f86])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(sK8(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f272,plain,
    ( ~ spl11_13
    | ~ spl11_15 ),
    inference(avatar_split_clause,[],[f123,f270,f264])).

fof(f123,plain,
    ( ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ r2_hidden(sK8(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f87,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1,X2),X0)
      | ~ r2_hidden(sK8(X0,X1,X2),X2)
      | sQ10_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f69,f86])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1,X2),X0)
      | ~ r2_hidden(sK8(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
