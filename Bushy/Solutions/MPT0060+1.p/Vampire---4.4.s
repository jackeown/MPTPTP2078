%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t53_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:28 EDT 2019

% Result     : Theorem 8.06s
% Output     : Refutation 8.06s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 176 expanded)
%              Number of leaves         :   11 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  154 ( 403 expanded)
%              Number of equality atoms :   22 (  75 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80662,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f735,f7152,f17115,f80642])).

fof(f80642,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f80527])).

fof(f80527,plain,
    ( $false
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f198,f3519,f9565,f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox/benchmark/xboole_1__t53_xboole_1.p',d3_xboole_0)).

fof(f9565,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f160,f197,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t53_xboole_1.p',d5_xboole_0)).

fof(f197,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f175,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f175,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f39,f160,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t53_xboole_1.p',d4_xboole_0)).

fof(f39,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t53_xboole_1.p',t53_xboole_1)).

fof(f160,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl7_5
  <=> ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f3519,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f176,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f176,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK2))
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f39,f160,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f198,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f175,f83])).

fof(f17115,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f17097])).

fof(f17097,plain,
    ( $false
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f7296,f7297,f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f7297,plain,
    ( ~ r2_hidden(sK6(sK2,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f7292,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t53_xboole_1.p',d3_tarski)).

fof(f7292,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f7248,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t53_xboole_1.p',t34_xboole_1)).

fof(f7248,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK2))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f6935,f7006,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7006,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f39,f6935,f42])).

fof(f6935,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK2))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f154,f154,f82])).

fof(f154,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK0,sK2),X0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl7_2
  <=> ! [X0] : ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK0,sK2),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f7296,plain,
    ( r2_hidden(sK6(sK2,k2_xboole_0(sK1,sK2)),sK2)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f7292,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7152,plain,(
    ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f7148])).

fof(f7148,plain,
    ( $false
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f66,f7100,f56])).

fof(f7100,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f6837,f6899,f70])).

fof(f6899,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f39,f6837,f41])).

fof(f6837,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl7_8 ),
    inference(superposition,[],[f734,f48])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t53_xboole_1.p',idempotence_k3_xboole_0)).

fof(f734,plain,
    ( ! [X1] : ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(X1,k4_xboole_0(sK0,sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f733])).

fof(f733,plain,
    ( spl7_8
  <=> ! [X1] : ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(X1,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t53_xboole_1.p',t7_xboole_1)).

fof(f735,plain,
    ( spl7_8
    | spl7_2
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f132,f159,f153,f733])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
      | ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK0,sK2),X0))
      | ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k3_xboole_0(X1,k4_xboole_0(sK0,sK1))) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X14,X15,X16] :
      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X14
      | ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),X14),X14)
      | ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),X14),k4_xboole_0(k4_xboole_0(sK0,sK2),X15))
      | ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),X14),k3_xboole_0(X16,k4_xboole_0(sK0,sK1))) ) ),
    inference(resolution,[],[f94,f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f94,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),X2),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),X2),X2)
      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X2
      | ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),X2),k4_xboole_0(k4_xboole_0(sK0,sK2),X3)) ) ),
    inference(resolution,[],[f90,f84])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),X0),k4_xboole_0(sK0,sK2))
      | k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),X0),X0)
      | ~ r2_hidden(sK3(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2),X0),k4_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f39,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
