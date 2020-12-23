%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t55_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:29 EDT 2019

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 334 expanded)
%              Number of leaves         :   29 ( 123 expanded)
%              Depth                    :    8
%              Number of atoms          :  381 ( 855 expanded)
%              Number of equality atoms :   26 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f463,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f174,f184,f189,f203,f208,f225,f270,f341,f365,f378,f379,f388,f395,f411,f415,f420,f425,f435,f440,f444,f448,f452,f455,f458,f460,f462])).

fof(f462,plain,
    ( ~ spl6_22
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl6_22
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f423,f417])).

fof(f417,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_28 ),
    inference(resolution,[],[f410,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t55_xboole_1.p',d4_xboole_0)).

fof(f410,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl6_28
  <=> r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f423,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_22 ),
    inference(resolution,[],[f387,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/xboole_1__t55_xboole_1.p',d5_xboole_0)).

fof(f387,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl6_22
  <=> r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f460,plain,
    ( ~ spl6_28
    | spl6_31 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | ~ spl6_28
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f417,f434])).

fof(f434,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl6_31
  <=> ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f458,plain,
    ( spl6_3
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f387,f428])).

fof(f428,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f167,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t55_xboole_1.p',d3_xboole_0)).

fof(f167,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl6_3
  <=> ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f455,plain,
    ( ~ spl6_4
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f410,f438])).

fof(f438,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl6_4 ),
    inference(resolution,[],[f170,f68])).

fof(f170,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl6_4
  <=> r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f452,plain,
    ( spl6_7
    | spl6_23
    | spl6_29
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_23
    | ~ spl6_29
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f431,f450])).

fof(f450,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_7
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f421,f449])).

fof(f449,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f441,f443])).

fof(f443,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_29 ),
    inference(resolution,[],[f407,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f407,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl6_29
  <=> ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f441,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl6_23 ),
    inference(resolution,[],[f384,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f384,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl6_23
  <=> ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f421,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f183,f67])).

fof(f183,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl6_7
  <=> ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f431,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl6_30
  <=> r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f448,plain,
    ( spl6_23
    | ~ spl6_26
    | spl6_31 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f446,f434])).

fof(f446,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f445,f442])).

fof(f442,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl6_23
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f441,f434])).

fof(f445,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_26 ),
    inference(resolution,[],[f401,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f401,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl6_26
  <=> r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f444,plain,
    ( spl6_26
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f437,f169,f400])).

fof(f437,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))
    | ~ spl6_4 ),
    inference(resolution,[],[f170,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f440,plain,
    ( ~ spl6_4
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f437,f404])).

fof(f404,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl6_27
  <=> ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f435,plain,
    ( ~ spl6_31
    | spl6_27 ),
    inference(avatar_split_clause,[],[f412,f403,f433])).

fof(f412,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_27 ),
    inference(resolution,[],[f404,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f425,plain,
    ( ~ spl6_22
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl6_22
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f422,f413])).

fof(f413,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl6_27 ),
    inference(resolution,[],[f404,f61])).

fof(f422,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl6_22 ),
    inference(resolution,[],[f387,f69])).

fof(f420,plain,
    ( ~ spl6_6
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f418,f397])).

fof(f397,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f180,f68])).

fof(f180,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl6_6
  <=> r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f418,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl6_28 ),
    inference(resolution,[],[f410,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f415,plain,
    ( ~ spl6_6
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f412,f396])).

fof(f396,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f180,f69])).

fof(f411,plain,
    ( ~ spl6_27
    | spl6_28
    | spl6_5 ),
    inference(avatar_split_clause,[],[f186,f172,f409,f403])).

fof(f172,plain,
    ( spl6_5
  <=> ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f186,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(resolution,[],[f173,f67])).

fof(f173,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f395,plain,
    ( ~ spl6_25
    | spl6_15
    | spl6_17
    | spl6_19 ),
    inference(avatar_split_clause,[],[f371,f363,f339,f268,f393])).

fof(f393,plain,
    ( spl6_25
  <=> ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f268,plain,
    ( spl6_15
  <=> ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f339,plain,
    ( spl6_17
  <=> ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f363,plain,
    ( spl6_19
  <=> ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f371,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f370,f369])).

fof(f369,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f368,f367])).

fof(f367,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | ~ spl6_15 ),
    inference(resolution,[],[f269,f64])).

fof(f269,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f268])).

fof(f368,plain,
    ( r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | ~ spl6_17 ),
    inference(resolution,[],[f340,f67])).

fof(f340,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f339])).

fof(f370,plain,
    ( r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | ~ spl6_19 ),
    inference(resolution,[],[f364,f67])).

fof(f364,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,sK0))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f363])).

fof(f388,plain,
    ( spl6_22
    | ~ spl6_2
    | spl6_7 ),
    inference(avatar_split_clause,[],[f381,f182,f163,f386])).

fof(f163,plain,
    ( spl6_2
  <=> r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f381,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0))
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f380,f183])).

fof(f380,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0))
    | r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(resolution,[],[f164,f63])).

fof(f164,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f163])).

fof(f379,plain,
    ( spl6_2
    | spl6_1
    | spl6_5 ),
    inference(avatar_split_clause,[],[f190,f172,f74,f163])).

fof(f74,plain,
    ( spl6_1
  <=> k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f190,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f185,f75])).

fof(f75,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f185,plain,
    ( r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(resolution,[],[f173,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t55_xboole_1.p',t2_tarski)).

fof(f378,plain,
    ( ~ spl6_21
    | spl6_15
    | spl6_17 ),
    inference(avatar_split_clause,[],[f369,f339,f268,f376])).

fof(f376,plain,
    ( spl6_21
  <=> ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f365,plain,
    ( ~ spl6_19
    | spl6_11 ),
    inference(avatar_split_clause,[],[f214,f201,f363])).

fof(f201,plain,
    ( spl6_11
  <=> ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f214,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,sK0))
    | ~ spl6_11 ),
    inference(resolution,[],[f202,f61])).

fof(f202,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f201])).

fof(f341,plain,
    ( ~ spl6_17
    | spl6_11 ),
    inference(avatar_split_clause,[],[f213,f201,f339])).

fof(f213,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,sK1))
    | ~ spl6_11 ),
    inference(resolution,[],[f202,f62])).

fof(f270,plain,
    ( ~ spl6_15
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f211,f192,f268])).

fof(f192,plain,
    ( spl6_8
  <=> r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f211,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f193,f68])).

fof(f193,plain,
    ( r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f192])).

fof(f225,plain,
    ( spl6_12
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f210,f192,f223])).

fof(f223,plain,
    ( spl6_12
  <=> r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f210,plain,
    ( r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f193,f69])).

fof(f208,plain,
    ( spl6_1
    | spl6_9
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f206,f75])).

fof(f206,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f204,f202])).

fof(f204,plain,
    ( r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | ~ spl6_9 ),
    inference(resolution,[],[f196,f50])).

fof(f196,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_9
  <=> ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f203,plain,
    ( ~ spl6_9
    | ~ spl6_11
    | spl6_1 ),
    inference(avatar_split_clause,[],[f154,f74,f201,f195])).

fof(f154,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ r2_hidden(sK5(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl6_1 ),
    inference(extensionality_resolution,[],[f51,f75])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f189,plain,
    ( spl6_1
    | spl6_3
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f187,f75])).

fof(f187,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f185,f167])).

fof(f184,plain,
    ( ~ spl6_7
    | spl6_3 ),
    inference(avatar_split_clause,[],[f176,f166,f182])).

fof(f176,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f167,f62])).

fof(f174,plain,
    ( ~ spl6_3
    | ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f153,f74,f172,f166])).

fof(f153,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ r2_hidden(sK5(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl6_1 ),
    inference(extensionality_resolution,[],[f51,f75])).

fof(f76,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t55_xboole_1.p',t55_xboole_1)).
%------------------------------------------------------------------------------
