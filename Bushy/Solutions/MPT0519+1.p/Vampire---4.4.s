%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t119_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:48 EDT 2019

% Result     : Theorem 21.42s
% Output     : Refutation 21.42s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 127 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  198 ( 304 expanded)
%              Number of equality atoms :   18 (  47 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f322,f351,f533,f1178,f1180,f1182])).

fof(f1182,plain,
    ( ~ spl12_12
    | spl12_19 ),
    inference(avatar_contradiction_clause,[],[f1181])).

fof(f1181,plain,
    ( $false
    | ~ spl12_12
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f1177,f767])).

fof(f767,plain,
    ( r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k2_relat_1(sK1))
    | ~ spl12_12 ),
    inference(resolution,[],[f556,f173])).

fof(f173,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(k8_relat_1(X6,sK1)))
      | r2_hidden(X5,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f127,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/relat_1__t119_relat_1.p',d3_tarski)).

fof(f127,plain,(
    ! [X2] : r1_tarski(k2_relat_1(k8_relat_1(X2,sK1)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f51,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t119_relat_1.p',t118_relat_1)).

fof(f51,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != k3_xboole_0(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t119_relat_1.p',t119_relat_1)).

fof(f556,plain,
    ( r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k2_relat_1(k8_relat_1(sK0,sK1)))
    | ~ spl12_12 ),
    inference(resolution,[],[f350,f100])).

fof(f100,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t119_relat_1.p',d5_relat_1)).

fof(f350,plain,
    ( r2_hidden(k4_tarski(sK8(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),k8_relat_1(sK0,sK1))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl12_12
  <=> r2_hidden(k4_tarski(sK8(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f1177,plain,
    ( ~ r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k2_relat_1(sK1))
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f1176])).

fof(f1176,plain,
    ( spl12_19
  <=> ~ r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f1180,plain,
    ( ~ spl12_12
    | spl12_17 ),
    inference(avatar_contradiction_clause,[],[f1179])).

fof(f1179,plain,
    ( $false
    | ~ spl12_12
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f1171,f553])).

fof(f553,plain,
    ( r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0)
    | ~ spl12_12 ),
    inference(resolution,[],[f350,f139])).

fof(f139,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X11,X10),k8_relat_1(X9,sK1))
      | r2_hidden(X10,X9) ) ),
    inference(subsumption_resolution,[],[f130,f125])).

fof(f125,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(resolution,[],[f51,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t119_relat_1.p',dt_k8_relat_1)).

fof(f130,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_relat_1(k8_relat_1(X9,sK1))
      | r2_hidden(X10,X9)
      | ~ r2_hidden(k4_tarski(X11,X10),k8_relat_1(X9,sK1)) ) ),
    inference(resolution,[],[f51,f96])).

fof(f96,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t119_relat_1.p',d12_relat_1)).

fof(f1171,plain,
    ( ~ r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0)
    | ~ spl12_17 ),
    inference(avatar_component_clause,[],[f1170])).

fof(f1170,plain,
    ( spl12_17
  <=> ~ r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f1178,plain,
    ( ~ spl12_17
    | ~ spl12_19
    | spl12_9 ),
    inference(avatar_split_clause,[],[f544,f317,f1176,f1170])).

fof(f317,plain,
    ( spl12_9
  <=> ~ r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k3_xboole_0(k2_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f544,plain,
    ( ~ r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k2_relat_1(sK1))
    | ~ r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0)
    | ~ spl12_9 ),
    inference(resolution,[],[f318,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t119_relat_1.p',d4_xboole_0)).

fof(f318,plain,
    ( ~ r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k3_xboole_0(k2_relat_1(sK1),sK0))
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f317])).

fof(f533,plain,
    ( ~ spl12_8
    | ~ spl12_10 ),
    inference(avatar_contradiction_clause,[],[f532])).

fof(f532,plain,
    ( $false
    | ~ spl12_8
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f521,f377])).

fof(f377,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK1)
    | ~ spl12_8
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f367,f354])).

fof(f354,plain,
    ( r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0)
    | ~ spl12_8 ),
    inference(resolution,[],[f315,f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f315,plain,
    ( r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k3_xboole_0(k2_relat_1(sK1),sK0))
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl12_8
  <=> r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k3_xboole_0(k2_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK1)
        | ~ r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0) )
    | ~ spl12_10 ),
    inference(resolution,[],[f321,f137])).

fof(f137,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k4_tarski(X5,X4),k8_relat_1(X3,sK1))
      | ~ r2_hidden(k4_tarski(X5,X4),sK1)
      | ~ r2_hidden(X4,X3) ) ),
    inference(subsumption_resolution,[],[f128,f125])).

fof(f128,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(k8_relat_1(X3,sK1))
      | ~ r2_hidden(X4,X3)
      | ~ r2_hidden(k4_tarski(X5,X4),sK1)
      | r2_hidden(k4_tarski(X5,X4),k8_relat_1(X3,sK1)) ) ),
    inference(resolution,[],[f51,f94])).

fof(f94,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f321,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),k8_relat_1(sK0,sK1))
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl12_10
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f521,plain,
    ( r2_hidden(k4_tarski(sK7(sK1,sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK1)
    | ~ spl12_8 ),
    inference(resolution,[],[f353,f99])).

fof(f99,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f353,plain,
    ( r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k2_relat_1(sK1))
    | ~ spl12_8 ),
    inference(resolution,[],[f315,f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f351,plain,
    ( spl12_8
    | spl12_12 ),
    inference(avatar_split_clause,[],[f158,f349,f314])).

fof(f158,plain,
    ( r2_hidden(k4_tarski(sK8(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),k8_relat_1(sK0,sK1))
    | r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k3_xboole_0(k2_relat_1(sK1),sK0)) ),
    inference(resolution,[],[f107,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | sQ11_eqProxy(k2_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f79,f106])).

fof(f106,plain,(
    ! [X1,X0] :
      ( sQ11_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f107,plain,(
    ~ sQ11_eqProxy(k2_relat_1(k8_relat_1(sK0,sK1)),k3_xboole_0(k2_relat_1(sK1),sK0)) ),
    inference(equality_proxy_replacement,[],[f52,f106])).

fof(f52,plain,(
    k2_relat_1(k8_relat_1(sK0,sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f322,plain,
    ( ~ spl12_9
    | spl12_10 ),
    inference(avatar_split_clause,[],[f159,f320,f317])).

fof(f159,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),k8_relat_1(sK0,sK1))
      | ~ r2_hidden(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k3_xboole_0(k2_relat_1(sK1),sK0)) ) ),
    inference(resolution,[],[f107,f116])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | sQ11_eqProxy(k2_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f80,f106])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
