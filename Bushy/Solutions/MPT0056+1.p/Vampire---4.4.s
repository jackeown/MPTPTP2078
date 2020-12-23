%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t49_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:28 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 234 expanded)
%              Number of leaves         :   25 (  86 expanded)
%              Depth                    :    7
%              Number of atoms          :  293 ( 588 expanded)
%              Number of equality atoms :   22 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f126,f133,f149,f156,f165,f191,f234,f259,f266,f278,f289,f300,f314,f318,f321,f324,f334,f337,f340,f343])).

fof(f343,plain,
    ( spl6_3
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f332,f341])).

fof(f341,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f326,f265])).

fof(f265,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl6_18
  <=> r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f326,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f119,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t49_xboole_1.p',d5_xboole_0)).

fof(f119,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_3
  <=> ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f332,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_20 ),
    inference(resolution,[],[f277,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f277,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl6_20
  <=> r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f340,plain,
    ( spl6_3
    | spl6_13
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_13
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f265,f338])).

fof(f338,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f326,f190])).

fof(f190,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl6_13
  <=> ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f337,plain,
    ( ~ spl6_10
    | spl6_19
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f335,f155])).

fof(f155,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_10
  <=> r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f335,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f330,f331])).

fof(f331,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_20 ),
    inference(resolution,[],[f277,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f330,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1)
    | ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_19 ),
    inference(resolution,[],[f262,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t49_xboole_1.p',d4_xboole_0)).

fof(f262,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl6_19
  <=> ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f334,plain,
    ( ~ spl6_20
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl6_20
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f331,f310])).

fof(f310,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl6_27
  <=> ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f324,plain,
    ( spl6_5
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f306,f322])).

fof(f322,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_5
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f282,f277])).

fof(f282,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f125,f46])).

fof(f125,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_5
  <=> ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f306,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_18 ),
    inference(resolution,[],[f265,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f321,plain,
    ( spl6_5
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f277,f319])).

fof(f319,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f282,f155])).

fof(f318,plain,
    ( spl6_13
    | spl6_21
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl6_13
    | ~ spl6_21
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f316,f313])).

fof(f313,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl6_26
  <=> r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f316,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_13
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f315,f190])).

fof(f315,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_21 ),
    inference(resolution,[],[f274,f49])).

fof(f274,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl6_21
  <=> ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f314,plain,
    ( spl6_26
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f307,f264,f312])).

fof(f307,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_18 ),
    inference(resolution,[],[f265,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f300,plain,
    ( spl6_24
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f167,f138,f298])).

fof(f298,plain,
    ( spl6_24
  <=> r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f138,plain,
    ( spl6_6
  <=> r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f167,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl6_6 ),
    inference(resolution,[],[f139,f47])).

fof(f139,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f289,plain,
    ( spl6_22
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f238,f144,f287])).

fof(f287,plain,
    ( spl6_22
  <=> r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f144,plain,
    ( spl6_8
  <=> r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f238,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f145,f51])).

fof(f145,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f278,plain,
    ( spl6_20
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f136,f121,f276])).

fof(f121,plain,
    ( spl6_4
  <=> r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f136,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl6_4 ),
    inference(resolution,[],[f122,f47])).

fof(f122,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f266,plain,
    ( spl6_18
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f157,f115,f264])).

fof(f115,plain,
    ( spl6_2
  <=> r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f157,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(resolution,[],[f116,f51])).

fof(f116,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f259,plain,
    ( ~ spl6_17
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f239,f144,f257])).

fof(f257,plain,
    ( spl6_17
  <=> ~ r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f239,plain,
    ( ~ r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f145,f50])).

fof(f234,plain,
    ( spl6_14
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f166,f138,f232])).

fof(f232,plain,
    ( spl6_14
  <=> r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f166,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f139,f48])).

fof(f191,plain,
    ( ~ spl6_13
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f158,f115,f189])).

fof(f158,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f116,f50])).

fof(f165,plain,
    ( spl6_1
    | spl6_7
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f163,f57])).

fof(f57,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_1
  <=> k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f163,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f161,f148])).

fof(f148,plain,
    ( ~ r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_9
  <=> ~ r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f161,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl6_7 ),
    inference(resolution,[],[f142,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t49_xboole_1.p',t2_tarski)).

fof(f142,plain,
    ( ~ r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_7
  <=> ~ r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f156,plain,
    ( spl6_10
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f135,f121,f154])).

fof(f135,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f122,f48])).

fof(f149,plain,
    ( ~ spl6_7
    | ~ spl6_9
    | spl6_1 ),
    inference(avatar_split_clause,[],[f108,f56,f147,f141])).

fof(f108,plain,
    ( ~ r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ r2_hidden(sK5(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl6_1 ),
    inference(extensionality_resolution,[],[f39,f57])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f133,plain,
    ( spl6_1
    | spl6_3
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f131,f57])).

fof(f131,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f129,f119])).

fof(f129,plain,
    ( r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f125,f38])).

fof(f126,plain,
    ( ~ spl6_3
    | ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f107,f56,f124,f118])).

fof(f107,plain,
    ( ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK5(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl6_1 ),
    inference(extensionality_resolution,[],[f39,f57])).

fof(f58,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) != k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t49_xboole_1.p',t49_xboole_1)).
%------------------------------------------------------------------------------
