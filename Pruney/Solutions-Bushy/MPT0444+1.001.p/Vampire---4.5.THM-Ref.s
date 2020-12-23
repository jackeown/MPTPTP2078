%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0444+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:00 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   39 (  69 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 154 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f69,f85])).

fof(f85,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f39,f73,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f73,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK0)
    | spl8_2 ),
    inference(resolution,[],[f58,f24])).

fof(f24,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f58,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl8_2
  <=> r2_hidden(sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f39,plain,(
    r2_hidden(k4_tarski(sK4(k3_xboole_0(sK0,sK1),sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f37,f23])).

fof(f23,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    r2_hidden(sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f10,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f10,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0,X1] : r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f69,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f64,f60])).

fof(f60,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK1)
    | spl8_1 ),
    inference(resolution,[],[f54,f24])).

fof(f54,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK1))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_1
  <=> r2_hidden(sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f64,plain,(
    r2_hidden(k4_tarski(sK4(k3_xboole_0(sK0,sK1),sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK1) ),
    inference(resolution,[],[f39,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f59,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f42,f56,f52])).

fof(f42,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0))
    | ~ r2_hidden(sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK1)) ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    ~ r2_hidden(sK2(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(resolution,[],[f10,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
