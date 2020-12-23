%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t73_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:27 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 126 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  227 ( 381 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f87,f100,f112,f125,f186,f254,f340,f359])).

fof(f359,plain,
    ( ~ spl9_0
    | ~ spl9_2
    | spl9_13
    | ~ spl9_60 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_13
    | ~ spl9_60 ),
    inference(subsumption_resolution,[],[f357,f124])).

fof(f124,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl9_13
  <=> ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f357,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_60 ),
    inference(subsumption_resolution,[],[f356,f88])).

fof(f88,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl9_0 ),
    inference(resolution,[],[f82,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t73_funct_1.p',dt_k7_relat_1)).

fof(f82,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl9_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f356,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_60 ),
    inference(subsumption_resolution,[],[f355,f94])).

fof(f94,plain,
    ( ! [X1] : v1_funct_1(k7_relat_1(sK2,X1))
    | ~ spl9_0
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f91,f82])).

fof(f91,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | v1_funct_1(k7_relat_1(sK2,X1)) )
    | ~ spl9_2 ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t73_funct_1.p',fc8_funct_1)).

fof(f86,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl9_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f355,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl9_60 ),
    inference(resolution,[],[f339,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t73_funct_1.p',d5_funct_1)).

fof(f339,plain,
    ( sP4(k1_funct_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl9_60
  <=> sP4(k1_funct_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f340,plain,
    ( spl9_60
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f284,f252,f98,f85,f81,f338])).

fof(f98,plain,
    ( spl9_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f252,plain,
    ( spl9_38
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f284,plain,
    ( sP4(k1_funct_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f278,f188])).

fof(f188,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f95,f99])).

fof(f99,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f95,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | k1_funct_1(sK2,X2) = k1_funct_1(k7_relat_1(sK2,X3),X2) )
    | ~ spl9_0
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f92,f82])).

fof(f92,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X2,X3)
        | k1_funct_1(sK2,X2) = k1_funct_1(k7_relat_1(sK2,X3),X2) )
    | ~ spl9_2 ),
    inference(resolution,[],[f86,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,X1)
      | k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t73_funct_1.p',t72_funct_1)).

fof(f278,plain,
    ( sP4(k1_funct_1(k7_relat_1(sK2,sK1),sK0),k7_relat_1(sK2,sK1))
    | ~ spl9_38 ),
    inference(resolution,[],[f253,f77])).

fof(f77,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | sP4(k1_funct_1(X0,X3),X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f253,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f252])).

fof(f254,plain,
    ( spl9_38
    | ~ spl9_0
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f212,f184,f81,f252])).

fof(f184,plain,
    ( spl9_26
  <=> sP7(sK0,k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f212,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl9_0
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f211,f176])).

fof(f176,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK2,X1)) = k3_xboole_0(X1,k1_relat_1(sK2))
    | ~ spl9_0 ),
    inference(superposition,[],[f89,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t73_funct_1.p',commutativity_k3_xboole_0)).

fof(f89,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK2,X1)) = k3_xboole_0(k1_relat_1(sK2),X1)
    | ~ spl9_0 ),
    inference(resolution,[],[f82,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t73_funct_1.p',t90_relat_1)).

fof(f211,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ spl9_26 ),
    inference(resolution,[],[f185,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t73_funct_1.p',d4_xboole_0)).

fof(f185,plain,
    ( sP7(sK0,k1_relat_1(sK2),sK1)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f184])).

fof(f186,plain,
    ( spl9_26
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f165,f110,f98,f184])).

fof(f110,plain,
    ( spl9_8
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f165,plain,
    ( sP7(sK0,k1_relat_1(sK2),sK1)
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(resolution,[],[f104,f111])).

fof(f111,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | sP7(sK0,X0,sK1) )
    | ~ spl9_4 ),
    inference(resolution,[],[f99,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f125,plain,(
    ~ spl9_13 ),
    inference(avatar_split_clause,[],[f47,f123])).

fof(f47,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X0,X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
         => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t73_funct_1.p',t73_funct_1)).

fof(f112,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f45,f110])).

fof(f45,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f46,f98])).

fof(f46,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f44,f85])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f43,f81])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
