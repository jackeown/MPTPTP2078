%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0665+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 139 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  309 ( 487 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f67,f71,f75,f87,f91,f97,f111,f216,f250,f271,f289,f301])).

fof(f301,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | ~ spl7_11
    | spl7_38 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_11
    | spl7_38 ),
    inference(subsumption_resolution,[],[f299,f62])).

fof(f62,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_4
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f299,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_3
    | ~ spl7_11
    | spl7_38 ),
    inference(subsumption_resolution,[],[f297,f58])).

fof(f58,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl7_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f297,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_11
    | spl7_38 ),
    inference(resolution,[],[f288,f90])).

fof(f90,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,k3_xboole_0(X0,X1))
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_11
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X0)
        | ~ r2_hidden(X3,X1)
        | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f288,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | spl7_38 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl7_38
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f289,plain,
    ( ~ spl7_38
    | ~ spl7_1
    | ~ spl7_10
    | spl7_35 ),
    inference(avatar_split_clause,[],[f281,f269,f85,f49,f287])).

fof(f49,plain,
    ( spl7_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f85,plain,
    ( spl7_10
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f269,plain,
    ( spl7_35
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f281,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ spl7_1
    | ~ spl7_10
    | spl7_35 ),
    inference(subsumption_resolution,[],[f280,f50])).

fof(f50,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f280,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl7_10
    | spl7_35 ),
    inference(superposition,[],[f270,f86])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f85])).

fof(f270,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | spl7_35 ),
    inference(avatar_component_clause,[],[f269])).

fof(f271,plain,
    ( ~ spl7_35
    | ~ spl7_3
    | spl7_5
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f263,f248,f65,f57,f269])).

fof(f65,plain,
    ( spl7_5
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f248,plain,
    ( spl7_33
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X1)))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f263,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl7_3
    | spl7_5
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f259,f58])).

fof(f259,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK0,sK1)
    | spl7_5
    | ~ spl7_33 ),
    inference(resolution,[],[f249,f66])).

fof(f66,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X1)))
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f248])).

fof(f250,plain,
    ( spl7_33
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f223,f214,f53,f49,f248])).

fof(f53,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f214,plain,
    ( spl7_29
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k1_funct_1(X0,X2),k2_relat_1(k7_relat_1(X0,X1)))
        | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X0,X1)))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X2,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X1)))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f221,f50])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X1)))
        | ~ r2_hidden(X0,X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2
    | ~ spl7_29 ),
    inference(resolution,[],[f215,f54])).

fof(f54,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f215,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X0,X1)))
        | r2_hidden(k1_funct_1(X0,X2),k2_relat_1(k7_relat_1(X0,X1)))
        | ~ r2_hidden(X2,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( spl7_29
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f124,f109,f95,f73,f69,f214])).

fof(f69,plain,
    ( spl7_6
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f73,plain,
    ( spl7_7
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_funct_1(k7_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f95,plain,
    ( spl7_12
  <=> ! [X3,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X3,k1_relat_1(X0))
        | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f109,plain,
    ( spl7_15
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,X1)
        | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k1_funct_1(X0,X2),k2_relat_1(k7_relat_1(X0,X1)))
        | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X0,X1)))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X2,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f123,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k1_funct_1(X0,X2),k2_relat_1(k7_relat_1(X0,X1)))
        | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X0,X1)))
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X2,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f122,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k7_relat_1(X0,X1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f122,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k1_funct_1(X0,X2),k2_relat_1(k7_relat_1(X0,X1)))
        | ~ v1_funct_1(k7_relat_1(X0,X1))
        | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X0,X1)))
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X2,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(superposition,[],[f96,f110])).

fof(f110,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f96,plain,
    ( ! [X0,X3] :
        ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X3,k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f111,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f34,f109])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,X1)
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(f97,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f42,f95])).

fof(f42,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f91,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f45,f89])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f87,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f31,f85])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f75,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f71,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f67,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f23,f65])).

fof(f23,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X0,X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
         => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

fof(f63,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f21,f61])).

fof(f21,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f22,f57])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f20,f53])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
