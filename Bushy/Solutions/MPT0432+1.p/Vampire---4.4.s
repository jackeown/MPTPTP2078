%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t13_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:50 EDT 2019

% Result     : Theorem 18.79s
% Output     : Refutation 18.79s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 104 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  143 ( 258 expanded)
%              Number of equality atoms :   15 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f695,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f198,f199,f536,f666,f694])).

fof(f694,plain,
    ( spl10_9
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f693])).

fof(f693,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f681,f625])).

fof(f625,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),X0),sK0)
    | ~ spl10_9 ),
    inference(resolution,[],[f560,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t13_relat_1.p',d3_xboole_0)).

fof(f560,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),X0),k2_xboole_0(sK0,sK1))
    | ~ spl10_9 ),
    inference(resolution,[],[f174,f81])).

fof(f81,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t13_relat_1.p',d4_relat_1)).

fof(f174,plain,
    ( ~ r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl10_9
  <=> ~ r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f681,plain,
    ( r2_hidden(k4_tarski(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),sK5(sK0,sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))))),sK0)
    | ~ spl10_10 ),
    inference(resolution,[],[f177,f80])).

fof(f80,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f177,plain,
    ( r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK0))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl10_10
  <=> r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f666,plain,
    ( spl10_9
    | ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f655])).

fof(f655,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f560,f547,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f547,plain,
    ( r2_hidden(k4_tarski(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),sK5(sK1,sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))))),sK1)
    | ~ spl10_12 ),
    inference(resolution,[],[f194,f80])).

fof(f194,plain,
    ( r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK1))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl10_12
  <=> r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f536,plain,
    ( ~ spl10_8
    | spl10_11
    | spl10_13 ),
    inference(avatar_contradiction_clause,[],[f535])).

fof(f535,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f534,f207])).

fof(f207,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),X0),sK1)
    | ~ spl10_13 ),
    inference(resolution,[],[f197,f81])).

fof(f197,plain,
    ( ~ r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK1))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl10_13
  <=> ~ r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f534,plain,
    ( r2_hidden(k4_tarski(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),sK5(k2_xboole_0(sK0,sK1),sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))))),sK1)
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f522,f201])).

fof(f201,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),X0),sK0)
    | ~ spl10_11 ),
    inference(resolution,[],[f180,f81])).

fof(f180,plain,
    ( ~ r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK0))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl10_11
  <=> ~ r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f522,plain,
    ( r2_hidden(k4_tarski(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),sK5(k2_xboole_0(sK0,sK1),sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))))),sK0)
    | r2_hidden(k4_tarski(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),sK5(k2_xboole_0(sK0,sK1),sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))))),sK1)
    | ~ spl10_8 ),
    inference(resolution,[],[f214,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f214,plain,
    ( r2_hidden(k4_tarski(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),sK5(k2_xboole_0(sK0,sK1),sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))))),k2_xboole_0(sK0,sK1))
    | ~ spl10_8 ),
    inference(resolution,[],[f171,f80])).

fof(f171,plain,
    ( r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl10_8
  <=> r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f199,plain,
    ( spl10_8
    | spl10_12
    | spl10_10 ),
    inference(avatar_split_clause,[],[f109,f176,f193,f170])).

fof(f109,plain,
    ( r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK0))
    | r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK1))
    | r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f88,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | sQ9_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f73,f87])).

fof(f87,plain,(
    ! [X1,X0] :
      ( sQ9_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f88,plain,(
    ~ sQ9_eqProxy(k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f44,f87])).

fof(f44,plain,(
    k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) != k1_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) != k1_relat_1(k2_xboole_0(X0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t13_relat_1.p',t13_relat_1)).

fof(f198,plain,
    ( ~ spl10_9
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f108,f196,f173])).

fof(f108,plain,
    ( ~ r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK1))
    | ~ r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f88,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | sQ9_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f72,f87])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f181,plain,
    ( ~ spl10_9
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f107,f179,f173])).

fof(f107,plain,
    ( ~ r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(sK0))
    | ~ r2_hidden(sK7(k1_relat_1(sK0),k1_relat_1(sK1),k1_relat_1(k2_xboole_0(sK0,sK1))),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f88,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | sQ9_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f71,f87])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
