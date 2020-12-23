%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t154_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:52 EDT 2019

% Result     : Theorem 6.62s
% Output     : Refutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 120 expanded)
%              Number of leaves         :    6 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 300 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1143,f2076,f2264])).

fof(f2264,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f2260])).

fof(f2260,plain,
    ( $false
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f1142,f80,f543,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k9_relat_1(sK2,X2))
      | ~ r2_hidden(sK5(sK2,X0,X1),X2)
      | ~ r2_hidden(X1,k9_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f79,f77])).

fof(f77,plain,(
    ! [X8,X7] :
      ( r2_hidden(k4_tarski(sK5(sK2,X7,X8),X8),sK2)
      | ~ r2_hidden(X8,k9_relat_1(sK2,X7)) ) ),
    inference(resolution,[],[f39,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t154_relat_1.p',d13_relat_1)).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t154_relat_1.p',t154_relat_1)).

fof(f79,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK2)
      | ~ r2_hidden(X11,X13)
      | r2_hidden(X12,k9_relat_1(sK2,X13)) ) ),
    inference(resolution,[],[f39,f68])).

fof(f68,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f543,plain,(
    r2_hidden(sK5(sK2,k3_xboole_0(sK0,sK1),sK3(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK1) ),
    inference(unit_resulting_resolution,[],[f162,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t154_relat_1.p',d4_xboole_0)).

fof(f162,plain,(
    r2_hidden(sK5(sK2,k3_xboole_0(sK0,sK1),sK3(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f39,f80,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f40,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t154_relat_1.p',d3_tarski)).

fof(f40,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f1142,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f1141])).

fof(f1141,plain,
    ( spl9_3
  <=> ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f2076,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f2072])).

fof(f2072,plain,
    ( $false
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f1136,f80,f542,f87])).

fof(f542,plain,(
    r2_hidden(sK5(sK2,k3_xboole_0(sK0,sK1),sK3(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK0) ),
    inference(unit_resulting_resolution,[],[f162,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1136,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f1135])).

fof(f1135,plain,
    ( spl9_1
  <=> ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f1143,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f213,f1141,f1135])).

fof(f213,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f81,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f81,plain,(
    ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f40,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
