%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 155 expanded)
%              Number of leaves         :   18 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  282 ( 520 expanded)
%              Number of equality atoms :   43 (  96 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f777,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f112,f122,f136,f235,f744])).

fof(f744,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f707,f105,f71,f66,f56])).

fof(f56,plain,
    ( spl7_1
  <=> k1_funct_1(k7_relat_1(sK6,sK5),sK4) = k1_funct_1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f66,plain,
    ( spl7_3
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f71,plain,
    ( spl7_4
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f105,plain,
    ( spl7_5
  <=> r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f707,plain,
    ( k1_funct_1(k7_relat_1(sK6,sK5),sK4) = k1_funct_1(sK6,sK4)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f73,f68,f107,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(f107,plain,
    ( r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f68,plain,
    ( v1_funct_1(sK6)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f73,plain,
    ( v1_relat_1(sK6)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f235,plain,
    ( ~ spl7_4
    | spl7_5
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl7_4
    | spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f225,f106])).

fof(f106,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5)))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f225,plain,
    ( r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5)))
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f75,f135,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))
      | ~ sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ sP2(X2,X0,X1) )
        & ( sP2(X2,X0,X1)
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f135,plain,
    ( sP2(sK6,sK4,sK5)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_9
  <=> sP2(sK6,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f75,plain,
    ( ! [X0,X1] : sP3(X0,X1,sK6)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f73,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f13,f20,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( r2_hidden(X0,k1_relat_1(X2))
        & r2_hidden(X0,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f136,plain,
    ( spl7_9
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f123,f117,f61,f133])).

fof(f61,plain,
    ( spl7_2
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f117,plain,
    ( spl7_7
  <=> r2_hidden(sK4,k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f123,plain,
    ( sP2(sK6,sK4,sK5)
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f63,f119,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,k1_relat_1(X0))
          & r2_hidden(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f119,plain,
    ( r2_hidden(sK4,k1_relat_1(sK6))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f117])).

% (27927)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f63,plain,
    ( r2_hidden(sK4,sK5)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f122,plain,
    ( spl7_7
    | ~ spl7_3
    | ~ spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f121,f109,f71,f66,f117])).

fof(f109,plain,
    ( spl7_6
  <=> k1_xboole_0 = k1_funct_1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f121,plain,
    ( r2_hidden(sK4,k1_relat_1(sK6))
    | ~ spl7_3
    | ~ spl7_4
    | spl7_6 ),
    inference(subsumption_resolution,[],[f115,f77])).

fof(f77,plain,
    ( ! [X0,X1] : sP1(X0,X1,sK6)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f73,f68,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X2,X1,X0)
          & sP0(X0,X2,X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f17,f16])).

fof(f16,plain,(
    ! [X0,X2,X1] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> r2_hidden(k4_tarski(X1,X2),X0) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> k1_xboole_0 = X2 )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f115,plain,
    ( r2_hidden(sK4,k1_relat_1(sK6))
    | ~ sP1(k1_xboole_0,sK4,sK6)
    | spl7_6 ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK6))
    | ~ sP1(k1_xboole_0,sK4,sK6)
    | spl7_6 ),
    inference(superposition,[],[f111,f52])).

fof(f52,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_funct_1(X2,X1)
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X1) = X0
      | k1_xboole_0 != X0
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_funct_1(X2,X1) = X0
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | k1_funct_1(X2,X1) != X0 ) )
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ( ( k1_funct_1(X0,X1) = X2
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | k1_funct_1(X0,X1) != X2 ) )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP1(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f111,plain,
    ( k1_xboole_0 != k1_funct_1(sK6,sK4)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f112,plain,
    ( spl7_5
    | ~ spl7_6
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f103,f71,f66,f56,f109,f105])).

fof(f103,plain,
    ( k1_xboole_0 != k1_funct_1(sK6,sK4)
    | r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5)))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f102,f83])).

fof(f83,plain,
    ( ! [X2,X0,X1] : sP1(X0,X1,k7_relat_1(sK6,X2))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f78,f80,f42])).

fof(f80,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK6,X0))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f73,f68,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f78,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK6,X0))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f73,f68,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f102,plain,
    ( k1_xboole_0 != k1_funct_1(sK6,sK4)
    | r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5)))
    | ~ sP1(k1_xboole_0,sK4,k7_relat_1(sK6,sK5))
    | spl7_1 ),
    inference(superposition,[],[f58,f52])).

fof(f58,plain,
    ( k1_funct_1(k7_relat_1(sK6,sK5),sK4) != k1_funct_1(sK6,sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f74,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f33,f71])).

fof(f33,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_funct_1(k7_relat_1(sK6,sK5),sK4) != k1_funct_1(sK6,sK4)
    & r2_hidden(sK4,sK5)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f8,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
        & r2_hidden(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k7_relat_1(sK6,sK5),sK4) != k1_funct_1(sK6,sK4)
      & r2_hidden(sK4,sK5)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,X1)
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(f69,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f34,f66])).

fof(f34,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f35,f61])).

fof(f35,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f36,f56])).

fof(f36,plain,(
    k1_funct_1(k7_relat_1(sK6,sK5),sK4) != k1_funct_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:31:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (27922)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.46  % (27930)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.47  % (27919)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (27930)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (27928)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (27920)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f777,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f112,f122,f136,f235,f744])).
% 0.22/0.48  fof(f744,plain,(
% 0.22/0.48    spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f707,f105,f71,f66,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl7_1 <=> k1_funct_1(k7_relat_1(sK6,sK5),sK4) = k1_funct_1(sK6,sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl7_3 <=> v1_funct_1(sK6)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl7_4 <=> v1_relat_1(sK6)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    spl7_5 <=> r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.48  fof(f707,plain,(
% 0.22/0.48    k1_funct_1(k7_relat_1(sK6,sK5),sK4) = k1_funct_1(sK6,sK4) | (~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f73,f68,f107,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5))) | ~spl7_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f105])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    v1_funct_1(sK6) | ~spl7_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f66])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    v1_relat_1(sK6) | ~spl7_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f235,plain,(
% 0.22/0.48    ~spl7_4 | spl7_5 | ~spl7_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f234])).
% 0.22/0.48  fof(f234,plain,(
% 0.22/0.48    $false | (~spl7_4 | spl7_5 | ~spl7_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f225,f106])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    ~r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5))) | spl7_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f105])).
% 0.22/0.48  fof(f225,plain,(
% 0.22/0.48    r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5))) | (~spl7_4 | ~spl7_9)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f75,f135,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) | ~sP2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | ~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))))) | ~sP3(X0,X1,X2))),
% 0.22/0.48    inference(rectify,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X1,X0,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~sP3(X1,X0,X2))),
% 0.22/0.48    inference(nnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X1,X0,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> sP2(X2,X0,X1)) | ~sP3(X1,X0,X2))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    sP2(sK6,sK4,sK5) | ~spl7_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f133])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl7_9 <=> sP2(sK6,sK4,sK5)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sP3(X0,X1,sK6)) ) | ~spl7_4),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f73,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (sP3(X1,X0,X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(definition_folding,[],[f13,f20,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    spl7_9 | ~spl7_2 | ~spl7_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f123,f117,f61,f133])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl7_2 <=> r2_hidden(sK4,sK5)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    spl7_7 <=> r2_hidden(sK4,k1_relat_1(sK6))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    sP2(sK6,sK4,sK5) | (~spl7_2 | ~spl7_7)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f63,f119,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,k1_relat_1(X0)) & r2_hidden(X1,X2)) | ~sP2(X0,X1,X2)))),
% 0.22/0.48    inference(rectify,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~sP2(X2,X0,X1)))),
% 0.22/0.48    inference(flattening,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~sP2(X2,X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f19])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    r2_hidden(sK4,k1_relat_1(sK6)) | ~spl7_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f117])).
% 0.22/0.48  % (27927)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    r2_hidden(sK4,sK5) | ~spl7_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f61])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    spl7_7 | ~spl7_3 | ~spl7_4 | spl7_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f121,f109,f71,f66,f117])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    spl7_6 <=> k1_xboole_0 = k1_funct_1(sK6,sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    r2_hidden(sK4,k1_relat_1(sK6)) | (~spl7_3 | ~spl7_4 | spl7_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f115,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sP1(X0,X1,sK6)) ) | (~spl7_3 | ~spl7_4)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f73,f68,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (sP1(X2,X1,X0) & sP0(X0,X2,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(definition_folding,[],[f10,f17,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X2,X1] : ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~sP0(X0,X2,X1))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X2,X1,X0] : ((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0)) | ~sP1(X2,X1,X0))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    r2_hidden(sK4,k1_relat_1(sK6)) | ~sP1(k1_xboole_0,sK4,sK6) | spl7_6),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f114])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK4,k1_relat_1(sK6)) | ~sP1(k1_xboole_0,sK4,sK6) | spl7_6),
% 0.22/0.48    inference(superposition,[],[f111,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X2,X1] : (k1_xboole_0 = k1_funct_1(X2,X1) | r2_hidden(X1,k1_relat_1(X2)) | ~sP1(k1_xboole_0,X1,X2)) )),
% 0.22/0.48    inference(equality_resolution,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_funct_1(X2,X1) = X0 | k1_xboole_0 != X0 | r2_hidden(X1,k1_relat_1(X2)) | ~sP1(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((k1_funct_1(X2,X1) = X0 | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | k1_funct_1(X2,X1) != X0)) | r2_hidden(X1,k1_relat_1(X2)) | ~sP1(X0,X1,X2))),
% 0.22/0.48    inference(rectify,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0)) | ~sP1(X2,X1,X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f17])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    k1_xboole_0 != k1_funct_1(sK6,sK4) | spl7_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f109])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    spl7_5 | ~spl7_6 | spl7_1 | ~spl7_3 | ~spl7_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f103,f71,f66,f56,f109,f105])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    k1_xboole_0 != k1_funct_1(sK6,sK4) | r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5))) | (spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f102,f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (sP1(X0,X1,k7_relat_1(sK6,X2))) ) | (~spl7_3 | ~spl7_4)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f78,f80,f42])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X0] : (v1_funct_1(k7_relat_1(sK6,X0))) ) | (~spl7_3 | ~spl7_4)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f73,f68,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k7_relat_1(sK6,X0))) ) | (~spl7_3 | ~spl7_4)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f73,f68,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    k1_xboole_0 != k1_funct_1(sK6,sK4) | r2_hidden(sK4,k1_relat_1(k7_relat_1(sK6,sK5))) | ~sP1(k1_xboole_0,sK4,k7_relat_1(sK6,sK5)) | spl7_1),
% 0.22/0.48    inference(superposition,[],[f58,f52])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    k1_funct_1(k7_relat_1(sK6,sK5),sK4) != k1_funct_1(sK6,sK4) | spl7_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f56])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl7_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f71])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v1_relat_1(sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    k1_funct_1(k7_relat_1(sK6,sK5),sK4) != k1_funct_1(sK6,sK4) & r2_hidden(sK4,sK5) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f8,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(k7_relat_1(sK6,sK5),sK4) != k1_funct_1(sK6,sK4) & r2_hidden(sK4,sK5) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl7_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f66])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    v1_funct_1(sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl7_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f61])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    r2_hidden(sK4,sK5)),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ~spl7_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f56])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    k1_funct_1(k7_relat_1(sK6,sK5),sK4) != k1_funct_1(sK6,sK4)),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (27930)------------------------------
% 0.22/0.48  % (27930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27930)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (27930)Memory used [KB]: 11257
% 0.22/0.48  % (27930)Time elapsed: 0.064 s
% 0.22/0.48  % (27930)------------------------------
% 0.22/0.48  % (27930)------------------------------
% 0.22/0.48  % (27913)Success in time 0.125 s
%------------------------------------------------------------------------------
