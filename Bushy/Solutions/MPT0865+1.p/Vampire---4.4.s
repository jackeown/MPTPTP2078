%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t23_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:05 EDT 2019

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   33 (  47 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 106 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f61,f74,f77])).

fof(f77,plain,
    ( spl5_7
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f75,f60])).

fof(f60,plain,
    ( k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) != sK0
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_7
  <=> k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f75,plain,
    ( k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) = sK0
    | ~ spl5_12 ),
    inference(superposition,[],[f40,f73])).

fof(f73,plain,
    ( k4_tarski(sK2(sK0),sK3(sK0)) = sK0
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_12
  <=> k4_tarski(sK2(sK0),sK3(sK0)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f40,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) = k4_tarski(k1_mcart_1(k4_tarski(X1,X2)),k2_mcart_1(k4_tarski(X1,X2))) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t23_mcart_1.p',t8_mcart_1)).

fof(f74,plain,
    ( spl5_12
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f53,f46,f42,f72])).

fof(f42,plain,
    ( spl5_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f46,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f53,plain,
    ( k4_tarski(sK2(sK0),sK3(sK0)) = sK0
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f52,f43])).

fof(f43,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f42])).

fof(f52,plain,
    ( ~ v1_relat_1(sK1)
    | k4_tarski(sK2(sK0),sK3(sK0)) = sK0
    | ~ spl5_2 ),
    inference(resolution,[],[f47,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0)
      | k4_tarski(sK2(X1),sK3(X1)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t23_mcart_1.p',d1_relat_1)).

fof(f47,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f61,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
      & r2_hidden(X0,X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
      & r2_hidden(X0,X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,X1)
         => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t23_mcart_1.p',t23_mcart_1)).

fof(f48,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f30,f46])).

fof(f30,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f29,f42])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
