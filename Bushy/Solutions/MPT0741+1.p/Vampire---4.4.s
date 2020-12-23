%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t31_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:26 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  99 expanded)
%              Number of leaves         :   13 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :  164 ( 290 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f75,f82,f93,f104,f160,f171,f182,f193])).

fof(f193,plain,
    ( spl5_4
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f183,f158,f77])).

fof(f77,plain,
    ( spl5_4
  <=> v2_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f158,plain,
    ( spl5_34
  <=> r2_hidden(sK4(sK0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f183,plain,
    ( v2_ordinal1(sK0)
    | ~ spl5_34 ),
    inference(resolution,[],[f159,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t31_ordinal1.p',d3_ordinal1)).

fof(f159,plain,
    ( r2_hidden(sK4(sK0),sK3(sK0))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f158])).

fof(f182,plain,
    ( spl5_4
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f181,f155,f77])).

fof(f155,plain,
    ( spl5_32
  <=> sK3(sK0) = sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f181,plain,
    ( v2_ordinal1(sK0)
    | ~ spl5_32 ),
    inference(trivial_inequality_removal,[],[f179])).

fof(f179,plain,
    ( sK3(sK0) != sK3(sK0)
    | v2_ordinal1(sK0)
    | ~ spl5_32 ),
    inference(superposition,[],[f58,f156])).

fof(f156,plain,
    ( sK3(sK0) = sK4(sK0)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f155])).

fof(f58,plain,(
    ! [X0] :
      ( sK3(X0) != sK4(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f171,plain,
    ( spl5_4
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f161,f152,f77])).

fof(f152,plain,
    ( spl5_30
  <=> r2_hidden(sK3(sK0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f161,plain,
    ( v2_ordinal1(sK0)
    | ~ spl5_30 ),
    inference(resolution,[],[f153,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK4(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f153,plain,
    ( r2_hidden(sK3(sK0),sK4(sK0))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f152])).

fof(f160,plain,
    ( spl5_30
    | spl5_32
    | spl5_34
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f138,f91,f80,f158,f155,f152])).

fof(f80,plain,
    ( spl5_6
  <=> v3_ordinal1(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f91,plain,
    ( spl5_10
  <=> v3_ordinal1(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f138,plain,
    ( r2_hidden(sK4(sK0),sK3(sK0))
    | sK3(sK0) = sK4(sK0)
    | r2_hidden(sK3(sK0),sK4(sK0))
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(resolution,[],[f83,f92])).

fof(f92,plain,
    ( v3_ordinal1(sK3(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(sK4(sK0),X0)
        | sK4(sK0) = X0
        | r2_hidden(X0,sK4(sK0)) )
    | ~ spl5_6 ),
    inference(resolution,[],[f81,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t31_ordinal1.p',t24_ordinal1)).

fof(f81,plain,
    ( v3_ordinal1(sK4(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f104,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f102,f63])).

fof(f63,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_1
  <=> ~ v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f102,plain,
    ( v3_ordinal1(sK0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f101,f74])).

fof(f74,plain,
    ( v1_ordinal1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_2
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f101,plain,
    ( ~ v1_ordinal1(sK0)
    | v3_ordinal1(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f78,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t31_ordinal1.p',d4_ordinal1)).

fof(f78,plain,
    ( v2_ordinal1(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f93,plain,
    ( spl5_4
    | spl5_10 ),
    inference(avatar_split_clause,[],[f67,f91,f77])).

fof(f67,plain,
    ( v3_ordinal1(sK3(sK0))
    | v2_ordinal1(sK0) ),
    inference(resolution,[],[f35,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f35,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(X0)
      & ! [X1] :
          ( ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) ) )
       => v3_ordinal1(X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t31_ordinal1.p',t31_ordinal1)).

fof(f82,plain,
    ( spl5_4
    | spl5_6 ),
    inference(avatar_split_clause,[],[f66,f80,f77])).

fof(f66,plain,
    ( v3_ordinal1(sK4(sK0))
    | v2_ordinal1(sK0) ),
    inference(resolution,[],[f35,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f71,f73])).

fof(f71,plain,(
    v1_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f68,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t31_ordinal1.p',d2_ordinal1)).

fof(f68,plain,
    ( r1_tarski(sK1(sK0),sK0)
    | v1_ordinal1(sK0) ),
    inference(resolution,[],[f36,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r1_tarski(X1,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f37,f62])).

fof(f37,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
