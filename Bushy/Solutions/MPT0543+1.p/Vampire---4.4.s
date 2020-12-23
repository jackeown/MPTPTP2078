%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t145_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:50 EDT 2019

% Result     : Theorem 13.87s
% Output     : Refutation 13.87s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 121 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  173 ( 307 expanded)
%              Number of equality atoms :   25 (  67 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3413,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f361,f3366,f3373,f3405])).

fof(f3405,plain,
    ( spl8_7
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f3404])).

fof(f3404,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f3403,f351])).

fof(f351,plain,
    ( ~ r2_hidden(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl8_7
  <=> ~ r2_hidden(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f3403,plain,
    ( r2_hidden(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f3400,f59])).

fof(f59,plain,(
    k9_relat_1(sK1,sK0) != k9_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t145_relat_1.p',commutativity_k3_xboole_0)).

fof(f31,plain,(
    k9_relat_1(sK1,sK0) != k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t145_relat_1.p',t145_relat_1)).

fof(f3400,plain,
    ( k9_relat_1(sK1,sK0) = k9_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)))
    | r2_hidden(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl8_16 ),
    inference(duplicate_literal_removal,[],[f3381])).

fof(f3381,plain,
    ( k9_relat_1(sK1,sK0) = k9_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)))
    | r2_hidden(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | r2_hidden(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl8_16 ),
    inference(resolution,[],[f719,f318])).

fof(f318,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(sK1,X0,X1),X2)
      | k9_relat_1(sK1,X0) = X1
      | r2_hidden(sK5(sK1,X0,X1),X1)
      | r2_hidden(sK5(sK1,X0,X1),k9_relat_1(sK1,X2)) ) ),
    inference(subsumption_resolution,[],[f305,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f305,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(sK1,X0,X1),X1)
      | k9_relat_1(sK1,X0) = X1
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(sK7(sK1,X0,X1),X2)
      | r2_hidden(sK5(sK1,X0,X1),k9_relat_1(sK1,X2)) ) ),
    inference(resolution,[],[f65,f56])).

fof(f56,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t145_relat_1.p',d13_relat_1)).

fof(f65,plain,(
    ! [X12,X13] :
      ( r2_hidden(k4_tarski(sK7(sK1,X12,X13),sK5(sK1,X12,X13)),sK1)
      | r2_hidden(sK5(sK1,X12,X13),X13)
      | k9_relat_1(sK1,X12) = X13 ) ),
    inference(resolution,[],[f30,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f719,plain,
    ( r2_hidden(sK7(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),sK0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f718])).

fof(f718,plain,
    ( spl8_16
  <=> r2_hidden(sK7(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f3373,plain,
    ( ~ spl8_8
    | spl8_17 ),
    inference(avatar_contradiction_clause,[],[f3372])).

fof(f3372,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f360,f727])).

fof(f727,plain,
    ( ! [X0] : ~ r2_hidden(sK7(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k3_xboole_0(sK0,X0))
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f722,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t145_relat_1.p',d4_xboole_0)).

fof(f722,plain,
    ( ~ r2_hidden(sK7(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),sK0)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f721])).

fof(f721,plain,
    ( spl8_17
  <=> ~ r2_hidden(sK7(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f360,plain,
    ( r2_hidden(sK7(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl8_8
  <=> r2_hidden(sK7(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f3366,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f3365])).

fof(f3365,plain,
    ( $false
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f3347,f1446])).

fof(f1446,plain,
    ( r2_hidden(sK3(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f354,f994])).

fof(f994,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k9_relat_1(sK1,X3))
      | r2_hidden(sK3(X2,X3,sK1),k3_xboole_0(X3,k1_relat_1(sK1))) ) ),
    inference(duplicate_literal_removal,[],[f980])).

fof(f980,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k9_relat_1(sK1,X3))
      | r2_hidden(sK3(X2,X3,sK1),k3_xboole_0(X3,k1_relat_1(sK1)))
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) ) ),
    inference(resolution,[],[f83,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,sK1),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t145_relat_1.p',t143_relat_1)).

fof(f83,plain,(
    ! [X14,X12,X13] :
      ( ~ r2_hidden(sK3(X12,X13,sK1),X14)
      | ~ r2_hidden(X12,k9_relat_1(sK1,X13))
      | r2_hidden(sK3(X12,X13,sK1),k3_xboole_0(X13,X14)) ) ),
    inference(resolution,[],[f62,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(X4,X5,sK1),X5)
      | ~ r2_hidden(X4,k9_relat_1(sK1,X5)) ) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f354,plain,
    ( r2_hidden(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl8_6
  <=> r2_hidden(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f3347,plain,
    ( ~ r2_hidden(sK3(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f59,f354,f354,f132])).

fof(f132,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK5(sK1,X6,X7),X7)
      | ~ r2_hidden(sK3(sK5(sK1,X6,X7),X8,sK1),X6)
      | ~ r2_hidden(sK5(sK1,X6,X7),k9_relat_1(sK1,X8))
      | k9_relat_1(sK1,X6) = X7 ) ),
    inference(subsumption_resolution,[],[f123,f30])).

fof(f123,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK5(sK1,X6,X7),k9_relat_1(sK1,X8))
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(sK3(sK5(sK1,X6,X7),X8,sK1),X6)
      | ~ r2_hidden(sK5(sK1,X6,X7),X7)
      | k9_relat_1(sK1,X6) = X7 ) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK3(X2,X3,sK1),X2),sK1)
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) ) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f361,plain,
    ( spl8_6
    | spl8_8 ),
    inference(avatar_split_clause,[],[f345,f359,f353])).

fof(f345,plain,
    ( r2_hidden(sK7(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | r2_hidden(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X3] :
      ( k9_relat_1(sK1,sK0) != X3
      | r2_hidden(sK7(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),X3),k3_xboole_0(sK0,k1_relat_1(sK1)))
      | r2_hidden(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),X3),X3) ) ),
    inference(subsumption_resolution,[],[f75,f30])).

fof(f75,plain,(
    ! [X3] :
      ( k9_relat_1(sK1,sK0) != X3
      | ~ v1_relat_1(sK1)
      | r2_hidden(sK7(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),X3),k3_xboole_0(sK0,k1_relat_1(sK1)))
      | r2_hidden(sK5(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)),X3),X3) ) ),
    inference(superposition,[],[f59,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
