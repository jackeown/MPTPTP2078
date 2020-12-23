%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 239 expanded)
%              Number of leaves         :   30 ( 107 expanded)
%              Depth                    :    6
%              Number of atoms          :  425 ( 782 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f817,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f55,f59,f63,f67,f71,f75,f79,f83,f99,f117,f165,f203,f218,f223,f322,f341,f362,f377,f394,f775,f797,f816])).

fof(f816,plain,
    ( ~ spl8_30
    | spl8_5
    | ~ spl8_10
    | ~ spl8_105 ),
    inference(avatar_split_clause,[],[f811,f795,f73,f53,f213])).

fof(f213,plain,
    ( spl8_30
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f53,plain,
    ( spl8_5
  <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f73,plain,
    ( spl8_10
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f795,plain,
    ( spl8_105
  <=> r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f811,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl8_5
    | ~ spl8_10
    | ~ spl8_105 ),
    inference(subsumption_resolution,[],[f808,f54])).

fof(f54,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f808,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | ~ spl8_10
    | ~ spl8_105 ),
    inference(resolution,[],[f796,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        | ~ v1_relat_1(X0)
        | r1_tarski(X0,X1) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f796,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK3))
    | ~ spl8_105 ),
    inference(avatar_component_clause,[],[f795])).

fof(f797,plain,
    ( spl8_105
    | ~ spl8_53
    | ~ spl8_103 ),
    inference(avatar_split_clause,[],[f786,f773,f392,f795])).

fof(f392,plain,
    ( spl8_53
  <=> r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f773,plain,
    ( spl8_103
  <=> ! [X0] :
        ( ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X0)
        | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f786,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK3))
    | ~ spl8_53
    | ~ spl8_103 ),
    inference(resolution,[],[f774,f393])).

fof(f393,plain,
    ( r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1)
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f392])).

fof(f774,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X0)
        | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK3)) )
    | ~ spl8_103 ),
    inference(avatar_component_clause,[],[f773])).

fof(f775,plain,
    ( spl8_103
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f368,f339,f97,f37,f773])).

fof(f37,plain,
    ( spl8_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f97,plain,
    ( spl8_14
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X1)
        | ~ r2_hidden(X4,X0)
        | ~ r2_hidden(k4_tarski(X3,X4),X1)
        | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f339,plain,
    ( spl8_46
  <=> r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f368,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X0)
        | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK3)) )
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f366,f38])).

fof(f38,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f366,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X0)
        | ~ v1_relat_1(sK3)
        | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK3)) )
    | ~ spl8_14
    | ~ spl8_46 ),
    inference(resolution,[],[f340,f98])).

fof(f98,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X3,X4),X1)
        | ~ r2_hidden(X4,X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f340,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f339])).

fof(f394,plain,
    ( spl8_53
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_51 ),
    inference(avatar_split_clause,[],[f388,f375,f65,f41,f392])).

fof(f41,plain,
    ( spl8_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f65,plain,
    ( spl8_8
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X1)
        | r2_hidden(X4,X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f375,plain,
    ( spl8_51
  <=> r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f388,plain,
    ( r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1)
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f385,f42])).

fof(f42,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f385,plain,
    ( r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl8_8
    | ~ spl8_51 ),
    inference(resolution,[],[f376,f66])).

fof(f66,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))
        | r2_hidden(X4,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f376,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2))
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f375])).

fof(f377,plain,
    ( spl8_51
    | ~ spl8_4
    | ~ spl8_49 ),
    inference(avatar_split_clause,[],[f363,f360,f49,f375])).

fof(f49,plain,
    ( spl8_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f360,plain,
    ( spl8_49
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK2))
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f363,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2))
    | ~ spl8_4
    | ~ spl8_49 ),
    inference(resolution,[],[f361,f50])).

fof(f50,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK2)) )
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f360])).

fof(f362,plain,
    ( spl8_49
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f228,f216,f61,f41,f360])).

fof(f61,plain,
    ( spl8_7
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f216,plain,
    ( spl8_31
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0)
        | ~ r1_tarski(k8_relat_1(sK0,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f228,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK2))
        | ~ r1_tarski(sK0,X0) )
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f224,f42])).

fof(f224,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK2))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_7
    | ~ spl8_31 ),
    inference(resolution,[],[f217,f62])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK2),X0)
        | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0) )
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f216])).

fof(f341,plain,
    ( spl8_46
    | ~ spl8_3
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f330,f320,f45,f339])).

fof(f45,plain,
    ( spl8_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f320,plain,
    ( spl8_43
  <=> ! [X1] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1)
        | ~ r1_tarski(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f330,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3)
    | ~ spl8_3
    | ~ spl8_43 ),
    inference(resolution,[],[f321,f46])).

fof(f46,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f321,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1) )
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f320])).

fof(f322,plain,
    ( spl8_43
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f207,f201,f81,f41,f320])).

fof(f81,plain,
    ( spl8_12
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(X2,X3),X0)
        | r2_hidden(k4_tarski(X2,X3),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f201,plain,
    ( spl8_28
  <=> r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f207,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1)
        | ~ r1_tarski(sK2,X1) )
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f205,f42])).

fof(f205,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1)
        | ~ r1_tarski(sK2,X1) )
    | ~ spl8_12
    | ~ spl8_28 ),
    inference(resolution,[],[f202,f82])).

fof(f82,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X3),X0)
        | ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X2,X3),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f202,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f201])).

fof(f223,plain,
    ( ~ spl8_2
    | ~ spl8_6
    | spl8_30 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_6
    | spl8_30 ),
    inference(subsumption_resolution,[],[f220,f42])).

fof(f220,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl8_6
    | spl8_30 ),
    inference(resolution,[],[f214,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl8_6
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f214,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl8_30 ),
    inference(avatar_component_clause,[],[f213])).

fof(f218,plain,
    ( ~ spl8_30
    | spl8_31
    | spl8_5
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f153,f115,f53,f216,f213])).

fof(f115,plain,
    ( spl8_18
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2)
        | ~ r1_tarski(X0,X2)
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f153,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0)
        | ~ r1_tarski(k8_relat_1(sK0,sK2),X0)
        | ~ v1_relat_1(k8_relat_1(sK0,sK2)) )
    | spl8_5
    | ~ spl8_18 ),
    inference(resolution,[],[f116,f54])).

fof(f116,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X1)
        | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2)
        | ~ r1_tarski(X0,X2)
        | ~ v1_relat_1(X0) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f115])).

fof(f203,plain,
    ( spl8_28
    | ~ spl8_2
    | spl8_5
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f167,f163,f53,f41,f201])).

fof(f163,plain,
    ( spl8_23
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(X0,X1),X2),sK5(k8_relat_1(X0,X1),X2)),X1)
        | ~ v1_relat_1(X1)
        | r1_tarski(k8_relat_1(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f167,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2)
    | ~ spl8_2
    | spl8_5
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f166,f42])).

fof(f166,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2)
    | spl8_5
    | ~ spl8_23 ),
    inference(resolution,[],[f164,f54])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X1),X2)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK4(k8_relat_1(X0,X1),X2),sK5(k8_relat_1(X0,X1),X2)),X1) )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f163])).

fof(f165,plain,
    ( spl8_23
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f89,f77,f69,f57,f163])).

fof(f69,plain,
    ( spl8_9
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f77,plain,
    ( spl8_11
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(X3,X4),X1)
        | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(X0,X1),X2),sK5(k8_relat_1(X0,X1),X2)),X1)
        | ~ v1_relat_1(X1)
        | r1_tarski(k8_relat_1(X0,X1),X2) )
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f88,f58])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK4(k8_relat_1(X0,X1),X2),sK5(k8_relat_1(X0,X1),X2)),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(X0,X1))
        | r1_tarski(k8_relat_1(X0,X1),X2) )
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(resolution,[],[f78,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        | ~ v1_relat_1(X0)
        | r1_tarski(X0,X1) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f78,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))
        | r2_hidden(k4_tarski(X3,X4),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f117,plain,
    ( spl8_18
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f95,f81,f69,f115])).

fof(f95,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2)
        | ~ r1_tarski(X0,X2)
        | r1_tarski(X0,X1) )
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2)
        | ~ r1_tarski(X0,X2)
        | ~ v1_relat_1(X0)
        | r1_tarski(X0,X1) )
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(resolution,[],[f82,f70])).

fof(f99,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f33,f97])).

fof(f33,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f30,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f30,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f83,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f19,f81])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f79,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f31,f22])).

fof(f31,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f75,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f21,f73])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f20,f69])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f35,f65])).

fof(f35,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f32,f22])).

fof(f32,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

fof(f59,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f22,f57])).

fof(f55,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f17,f53])).

fof(f17,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

fof(f51,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f16,f49])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f15,f45])).

fof(f15,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f14,f37])).

fof(f14,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (26188)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (26192)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (26194)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (26185)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (26184)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (26195)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (26198)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (26183)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (26193)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (26181)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (26180)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (26179)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (26182)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (26180)Refutation not found, incomplete strategy% (26180)------------------------------
% 0.21/0.51  % (26180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26180)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26180)Memory used [KB]: 10490
% 0.21/0.51  % (26180)Time elapsed: 0.091 s
% 0.21/0.51  % (26180)------------------------------
% 0.21/0.51  % (26180)------------------------------
% 0.21/0.51  % (26187)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (26196)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (26186)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (26189)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (26200)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (26200)Refutation not found, incomplete strategy% (26200)------------------------------
% 0.21/0.52  % (26200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26190)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (26200)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26200)Memory used [KB]: 10490
% 0.21/0.52  % (26200)Time elapsed: 0.104 s
% 0.21/0.52  % (26200)------------------------------
% 0.21/0.52  % (26200)------------------------------
% 0.21/0.52  % (26188)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (26191)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (26199)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f817,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f55,f59,f63,f67,f71,f75,f79,f83,f99,f117,f165,f203,f218,f223,f322,f341,f362,f377,f394,f775,f797,f816])).
% 0.21/0.53  fof(f816,plain,(
% 0.21/0.53    ~spl8_30 | spl8_5 | ~spl8_10 | ~spl8_105),
% 0.21/0.53    inference(avatar_split_clause,[],[f811,f795,f73,f53,f213])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    spl8_30 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    spl8_5 <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl8_10 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r1_tarski(X0,X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.53  fof(f795,plain,(
% 0.21/0.53    spl8_105 <=> r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).
% 0.21/0.53  fof(f811,plain,(
% 0.21/0.53    ~v1_relat_1(k8_relat_1(sK0,sK2)) | (spl8_5 | ~spl8_10 | ~spl8_105)),
% 0.21/0.53    inference(subsumption_resolution,[],[f808,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f53])).
% 0.21/0.53  fof(f808,plain,(
% 0.21/0.53    ~v1_relat_1(k8_relat_1(sK0,sK2)) | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | (~spl8_10 | ~spl8_105)),
% 0.21/0.53    inference(resolution,[],[f796,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) ) | ~spl8_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f73])).
% 0.21/0.53  fof(f796,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK3)) | ~spl8_105),
% 0.21/0.53    inference(avatar_component_clause,[],[f795])).
% 0.21/0.53  fof(f797,plain,(
% 0.21/0.53    spl8_105 | ~spl8_53 | ~spl8_103),
% 0.21/0.53    inference(avatar_split_clause,[],[f786,f773,f392,f795])).
% 0.21/0.53  fof(f392,plain,(
% 0.21/0.53    spl8_53 <=> r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 0.21/0.53  fof(f773,plain,(
% 0.21/0.53    spl8_103 <=> ! [X0] : (~r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X0) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK3)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).
% 0.21/0.53  fof(f786,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK3)) | (~spl8_53 | ~spl8_103)),
% 0.21/0.53    inference(resolution,[],[f774,f393])).
% 0.21/0.53  fof(f393,plain,(
% 0.21/0.53    r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1) | ~spl8_53),
% 0.21/0.53    inference(avatar_component_clause,[],[f392])).
% 0.21/0.53  fof(f774,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X0) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK3))) ) | ~spl8_103),
% 0.21/0.53    inference(avatar_component_clause,[],[f773])).
% 0.21/0.53  fof(f775,plain,(
% 0.21/0.53    spl8_103 | ~spl8_1 | ~spl8_14 | ~spl8_46),
% 0.21/0.53    inference(avatar_split_clause,[],[f368,f339,f97,f37,f773])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    spl8_1 <=> v1_relat_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl8_14 <=> ! [X1,X3,X0,X4] : (~v1_relat_1(X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X1) | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.53  fof(f339,plain,(
% 0.21/0.53    spl8_46 <=> r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X0) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK3))) ) | (~spl8_1 | ~spl8_14 | ~spl8_46)),
% 0.21/0.53    inference(subsumption_resolution,[],[f366,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    v1_relat_1(sK3) | ~spl8_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f37])).
% 0.21/0.53  fof(f366,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X0) | ~v1_relat_1(sK3) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK3))) ) | (~spl8_14 | ~spl8_46)),
% 0.21/0.53    inference(resolution,[],[f340,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) ) | ~spl8_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3) | ~spl8_46),
% 0.21/0.53    inference(avatar_component_clause,[],[f339])).
% 0.21/0.53  fof(f394,plain,(
% 0.21/0.53    spl8_53 | ~spl8_2 | ~spl8_8 | ~spl8_51),
% 0.21/0.53    inference(avatar_split_clause,[],[f388,f375,f65,f41,f392])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    spl8_2 <=> v1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl8_8 <=> ! [X1,X3,X0,X4] : (~v1_relat_1(X1) | r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.53  fof(f375,plain,(
% 0.21/0.53    spl8_51 <=> r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 0.21/0.53  fof(f388,plain,(
% 0.21/0.53    r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1) | (~spl8_2 | ~spl8_8 | ~spl8_51)),
% 0.21/0.53    inference(subsumption_resolution,[],[f385,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    v1_relat_1(sK2) | ~spl8_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f41])).
% 0.21/0.53  fof(f385,plain,(
% 0.21/0.53    r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1) | ~v1_relat_1(sK2) | (~spl8_8 | ~spl8_51)),
% 0.21/0.53    inference(resolution,[],[f376,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) | r2_hidden(X4,X0) | ~v1_relat_1(X1)) ) | ~spl8_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f65])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2)) | ~spl8_51),
% 0.21/0.53    inference(avatar_component_clause,[],[f375])).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    spl8_51 | ~spl8_4 | ~spl8_49),
% 0.21/0.53    inference(avatar_split_clause,[],[f363,f360,f49,f375])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    spl8_4 <=> r1_tarski(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.53  fof(f360,plain,(
% 0.21/0.53    spl8_49 <=> ! [X0] : (r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK2)) | ~r1_tarski(sK0,X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 0.21/0.53  fof(f363,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2)) | (~spl8_4 | ~spl8_49)),
% 0.21/0.53    inference(resolution,[],[f361,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1) | ~spl8_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f49])).
% 0.21/0.53  fof(f361,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(sK0,X0) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK2))) ) | ~spl8_49),
% 0.21/0.53    inference(avatar_component_clause,[],[f360])).
% 0.21/0.53  fof(f362,plain,(
% 0.21/0.53    spl8_49 | ~spl8_2 | ~spl8_7 | ~spl8_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f228,f216,f61,f41,f360])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    spl8_7 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    spl8_31 <=> ! [X0] : (r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0) | ~r1_tarski(k8_relat_1(sK0,sK2),X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK2)) | ~r1_tarski(sK0,X0)) ) | (~spl8_2 | ~spl8_7 | ~spl8_31)),
% 0.21/0.53    inference(subsumption_resolution,[],[f224,f42])).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(X0,sK2)) | ~r1_tarski(sK0,X0) | ~v1_relat_1(sK2)) ) | (~spl8_7 | ~spl8_31)),
% 0.21/0.53    inference(resolution,[],[f217,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) ) | ~spl8_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f61])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k8_relat_1(sK0,sK2),X0) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0)) ) | ~spl8_31),
% 0.21/0.53    inference(avatar_component_clause,[],[f216])).
% 0.21/0.53  fof(f341,plain,(
% 0.21/0.53    spl8_46 | ~spl8_3 | ~spl8_43),
% 0.21/0.53    inference(avatar_split_clause,[],[f330,f320,f45,f339])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    spl8_3 <=> r1_tarski(sK2,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.53  fof(f320,plain,(
% 0.21/0.53    spl8_43 <=> ! [X1] : (r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1) | ~r1_tarski(sK2,X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 0.21/0.53  fof(f330,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3) | (~spl8_3 | ~spl8_43)),
% 0.21/0.53    inference(resolution,[],[f321,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    r1_tarski(sK2,sK3) | ~spl8_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f45])).
% 0.21/0.54  fof(f321,plain,(
% 0.21/0.54    ( ! [X1] : (~r1_tarski(sK2,X1) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1)) ) | ~spl8_43),
% 0.21/0.54    inference(avatar_component_clause,[],[f320])).
% 0.21/0.54  fof(f322,plain,(
% 0.21/0.54    spl8_43 | ~spl8_2 | ~spl8_12 | ~spl8_28),
% 0.21/0.54    inference(avatar_split_clause,[],[f207,f201,f81,f41,f320])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    spl8_12 <=> ! [X1,X3,X0,X2] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    spl8_28 <=> r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1) | ~r1_tarski(sK2,X1)) ) | (~spl8_2 | ~spl8_12 | ~spl8_28)),
% 0.21/0.54    inference(subsumption_resolution,[],[f205,f42])).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1) | ~r1_tarski(sK2,X1)) ) | (~spl8_12 | ~spl8_28)),
% 0.21/0.54    inference(resolution,[],[f202,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X0,X1)) ) | ~spl8_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f81])).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2) | ~spl8_28),
% 0.21/0.54    inference(avatar_component_clause,[],[f201])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    ~spl8_2 | ~spl8_6 | spl8_30),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f222])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    $false | (~spl8_2 | ~spl8_6 | spl8_30)),
% 0.21/0.54    inference(subsumption_resolution,[],[f220,f42])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | (~spl8_6 | spl8_30)),
% 0.21/0.54    inference(resolution,[],[f214,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl8_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    spl8_6 <=> ! [X1,X0] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl8_30),
% 0.21/0.54    inference(avatar_component_clause,[],[f213])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    ~spl8_30 | spl8_31 | spl8_5 | ~spl8_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f153,f115,f53,f216,f213])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    spl8_18 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0) | ~r1_tarski(k8_relat_1(sK0,sK2),X0) | ~v1_relat_1(k8_relat_1(sK0,sK2))) ) | (spl8_5 | ~spl8_18)),
% 0.21/0.54    inference(resolution,[],[f116,f54])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2) | ~r1_tarski(X0,X2) | ~v1_relat_1(X0)) ) | ~spl8_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f115])).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    spl8_28 | ~spl8_2 | spl8_5 | ~spl8_23),
% 0.21/0.54    inference(avatar_split_clause,[],[f167,f163,f53,f41,f201])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    spl8_23 <=> ! [X1,X0,X2] : (r2_hidden(k4_tarski(sK4(k8_relat_1(X0,X1),X2),sK5(k8_relat_1(X0,X1),X2)),X1) | ~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2) | (~spl8_2 | spl8_5 | ~spl8_23)),
% 0.21/0.54    inference(subsumption_resolution,[],[f166,f42])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2) | (spl8_5 | ~spl8_23)),
% 0.21/0.54    inference(resolution,[],[f164,f54])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X2) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK4(k8_relat_1(X0,X1),X2),sK5(k8_relat_1(X0,X1),X2)),X1)) ) | ~spl8_23),
% 0.21/0.54    inference(avatar_component_clause,[],[f163])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    spl8_23 | ~spl8_6 | ~spl8_9 | ~spl8_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f89,f77,f69,f57,f163])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl8_9 <=> ! [X1,X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r1_tarski(X0,X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl8_11 <=> ! [X1,X3,X0,X4] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(k8_relat_1(X0,X1),X2),sK5(k8_relat_1(X0,X1),X2)),X1) | ~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X2)) ) | (~spl8_6 | ~spl8_9 | ~spl8_11)),
% 0.21/0.54    inference(subsumption_resolution,[],[f88,f58])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(k8_relat_1(X0,X1),X2),sK5(k8_relat_1(X0,X1),X2)),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | r1_tarski(k8_relat_1(X0,X1),X2)) ) | (~spl8_9 | ~spl8_11)),
% 0.21/0.54    inference(resolution,[],[f78,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) ) | ~spl8_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f69])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) | r2_hidden(k4_tarski(X3,X4),X1) | ~v1_relat_1(X1)) ) | ~spl8_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f77])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    spl8_18 | ~spl8_9 | ~spl8_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f95,f81,f69,f115])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) ) | (~spl8_9 | ~spl8_12)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2) | ~r1_tarski(X0,X2) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) ) | (~spl8_9 | ~spl8_12)),
% 0.21/0.54    inference(resolution,[],[f82,f70])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl8_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f33,f97])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X1) | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f30,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X1) | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X1) | r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    spl8_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f19,f81])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    spl8_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f34,f77])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f31,f22])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl8_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f21,f73])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    spl8_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f20,f69])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl8_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f35,f65])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f32,f22])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    spl8_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f29,f61])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    spl8_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f22,f57])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ~spl8_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f17,f53])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f7])).
% 0.21/0.54  fof(f7,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f5])).
% 0.21/0.54  fof(f5,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    spl8_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f16,f49])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    spl8_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f15,f45])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    r1_tarski(sK2,sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    spl8_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f18,f41])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    v1_relat_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    spl8_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f14,f37])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    v1_relat_1(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (26188)------------------------------
% 0.21/0.54  % (26188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26188)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (26188)Memory used [KB]: 11257
% 0.21/0.54  % (26188)Time elapsed: 0.093 s
% 0.21/0.54  % (26188)------------------------------
% 0.21/0.54  % (26188)------------------------------
% 0.21/0.54  % (26172)Success in time 0.176 s
%------------------------------------------------------------------------------
