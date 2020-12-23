%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t137_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:15 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 427 expanded)
%              Number of leaves         :   29 ( 151 expanded)
%              Depth                    :   13
%              Number of atoms          :  553 (1401 expanded)
%              Number of equality atoms :   25 ( 118 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f72,f79,f131,f137,f152,f158,f165,f181,f204,f237,f262,f263,f275,f337,f428,f441,f562,f566,f574,f668,f1046,f1074,f1110,f1124,f1127])).

fof(f1127,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_13
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f1126])).

fof(f1126,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1125,f1122])).

fof(f1122,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1121,f64])).

fof(f64,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f1121,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1120,f274])).

fof(f274,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl6_22
  <=> r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f1120,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_2
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1119,f71])).

fof(f71,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1119,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_24 ),
    inference(resolution,[],[f336,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t137_funct_1.p',d13_funct_1)).

fof(f336,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl6_24
  <=> r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f1125,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_13
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1117,f440])).

fof(f440,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl6_28
  <=> r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f1117,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_13 ),
    inference(resolution,[],[f151,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t137_funct_1.p',d4_xboole_0)).

fof(f151,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_13
  <=> ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f1124,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_21
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f1123])).

fof(f1123,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1122,f258])).

fof(f258,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl6_21
  <=> ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f1110,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_20
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f1109])).

fof(f1109,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_20
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f1108,f261])).

fof(f261,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl6_20
  <=> r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f1108,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f1107,f64])).

fof(f1107,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_2
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f1106,f71])).

fof(f1106,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_25 ),
    inference(resolution,[],[f333,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f333,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl6_25
  <=> ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f1074,plain,
    ( ~ spl6_25
    | ~ spl6_0
    | ~ spl6_2
    | spl6_11
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f1044,f426,f273,f144,f70,f63,f332])).

fof(f144,plain,
    ( spl6_11
  <=> ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f426,plain,
    ( spl6_26
  <=> r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f1044,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f1043,f427])).

fof(f427,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f426])).

fof(f1043,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1042,f71])).

fof(f1042,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_0
    | ~ spl6_11
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1041,f64])).

fof(f1041,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_11
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1025,f274])).

fof(f1025,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_11 ),
    inference(resolution,[],[f219,f145])).

fof(f145,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f219,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_hidden(X4,k10_relat_1(X3,k3_xboole_0(X5,X6)))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(k1_funct_1(X3,X4),X6)
      | ~ r2_hidden(k1_funct_1(X3,X4),X5) ) ),
    inference(resolution,[],[f56,f53])).

fof(f1046,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_11
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f1045])).

fof(f1045,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f1044,f336])).

fof(f668,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_27
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f667])).

fof(f667,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_27
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f666,f440])).

fof(f666,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f665,f64])).

fof(f665,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_2
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f664,f71])).

fof(f664,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_27 ),
    inference(resolution,[],[f424,f57])).

fof(f424,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl6_27
  <=> ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f574,plain,
    ( spl6_22
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f564,f260,f70,f63,f273])).

fof(f564,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f563,f64])).

fof(f563,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f442,f71])).

fof(f442,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_20 ),
    inference(resolution,[],[f261,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f566,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_20
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f271,f564])).

fof(f271,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl6_23
  <=> ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f562,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_26
    | spl6_29 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_26
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f560,f437])).

fof(f437,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl6_29
  <=> ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f560,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f559,f64])).

fof(f559,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f558,f274])).

fof(f558,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_2
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f557,f71])).

fof(f557,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_26 ),
    inference(resolution,[],[f427,f56])).

fof(f441,plain,
    ( spl6_28
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f168,f147,f439])).

fof(f147,plain,
    ( spl6_12
  <=> r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f168,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_12 ),
    inference(resolution,[],[f148,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f148,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f428,plain,
    ( spl6_26
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f330,f141,f70,f63,f426])).

fof(f141,plain,
    ( spl6_10
  <=> r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f330,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f329,f71])).

fof(f329,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f321,f64])).

fof(f321,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f172,f142])).

fof(f142,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f172,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X5,k10_relat_1(X4,k3_xboole_0(X6,X7)))
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | r2_hidden(k1_funct_1(X4,X5),X7) ) ),
    inference(resolution,[],[f57,f54])).

fof(f337,plain,
    ( spl6_24
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f310,f141,f70,f63,f335])).

fof(f310,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f309,f71])).

fof(f309,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f301,f64])).

fof(f301,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f171,f142])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k10_relat_1(X0,k3_xboole_0(X2,X3)))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X1),X2) ) ),
    inference(resolution,[],[f57,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f275,plain,
    ( spl6_22
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f266,f141,f70,f63,f273])).

fof(f266,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f265,f64])).

fof(f265,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f264,f71])).

fof(f264,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f142,f58])).

fof(f263,plain,
    ( spl6_18
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f238,f163,f70,f63,f202])).

fof(f202,plain,
    ( spl6_18
  <=> r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f163,plain,
    ( spl6_14
  <=> r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f238,plain,
    ( r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k1_relat_1(sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f234,f64])).

fof(f234,plain,
    ( r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f233,f71])).

fof(f233,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(resolution,[],[f164,f58])).

fof(f164,plain,
    ( r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f163])).

fof(f262,plain,
    ( spl6_20
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f167,f147,f260])).

fof(f167,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_12 ),
    inference(resolution,[],[f148,f55])).

fof(f237,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_14
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_14
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f235,f64])).

fof(f235,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_14
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f234,f200])).

fof(f200,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k1_relat_1(sK2))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl6_19
  <=> ~ r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f204,plain,
    ( spl6_18
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f185,f126,f70,f63,f202])).

fof(f126,plain,
    ( spl6_8
  <=> r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f185,plain,
    ( r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k1_relat_1(sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f184,f64])).

fof(f184,plain,
    ( r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f183,f71])).

fof(f183,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f127,f58])).

fof(f127,plain,
    ( r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f181,plain,
    ( spl6_16
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f139,f120,f179])).

fof(f179,plain,
    ( spl6_16
  <=> r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f120,plain,
    ( spl6_6
  <=> r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f139,plain,
    ( r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_6 ),
    inference(resolution,[],[f121,f54])).

fof(f121,plain,
    ( r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f165,plain,
    ( spl6_14
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f138,f120,f163])).

fof(f138,plain,
    ( r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_6 ),
    inference(resolution,[],[f121,f55])).

fof(f158,plain,
    ( spl6_5
    | spl6_11
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f156,f78])).

fof(f78,plain,
    ( k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_5
  <=> k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f156,plain,
    ( k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f154,f145])).

fof(f154,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl6_13 ),
    inference(resolution,[],[f151,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t137_funct_1.p',t2_tarski)).

fof(f152,plain,
    ( ~ spl6_11
    | ~ spl6_13
    | spl6_5 ),
    inference(avatar_split_clause,[],[f112,f77,f150,f144])).

fof(f112,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK4(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl6_5 ),
    inference(extensionality_resolution,[],[f42,f78])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f137,plain,
    ( spl6_5
    | spl6_7
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f135,f78])).

fof(f135,plain,
    ( k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f133,f130])).

fof(f130,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_9
  <=> ~ r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f133,plain,
    ( r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(resolution,[],[f124,f41])).

fof(f124,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_7
  <=> ~ r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f131,plain,
    ( ~ spl6_7
    | ~ spl6_9
    | spl6_5 ),
    inference(avatar_split_clause,[],[f111,f77,f129,f123])).

fof(f111,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k10_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ r2_hidden(sK4(k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl6_5 ),
    inference(extensionality_resolution,[],[f42,f78])).

fof(f79,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != k10_relat_1(X2,k3_xboole_0(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != k10_relat_1(X2,k3_xboole_0(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t137_funct_1.p',t137_funct_1)).

fof(f72,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
