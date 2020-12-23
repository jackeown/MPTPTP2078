%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t42_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:13 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 132 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  255 ( 505 expanded)
%              Number of equality atoms :   22 (  47 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f84,f103,f107,f115,f149,f153,f184,f242,f243,f279,f299])).

fof(f299,plain,
    ( ~ spl9_0
    | spl9_21
    | ~ spl9_54 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_21
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f297,f152])).

fof(f152,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl9_21
  <=> ~ r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f297,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl9_0
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f296,f79])).

fof(f79,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl9_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f296,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl9_54 ),
    inference(resolution,[],[f278,f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t42_wellord1.p',d1_wellord1)).

fof(f278,plain,
    ( sP4(sK1,sK0,sK2)
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl9_54
  <=> sP4(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f279,plain,
    ( spl9_54
    | spl9_48
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f244,f237,f240,f277])).

fof(f240,plain,
    ( spl9_48
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f237,plain,
    ( spl9_46
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f244,plain,
    ( sK0 = sK1
    | sP4(sK1,sK0,sK2)
    | ~ spl9_46 ),
    inference(resolution,[],[f238,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | X1 = X3
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f238,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f237])).

fof(f243,plain,
    ( sK0 != sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(theory_axiom,[])).

fof(f242,plain,
    ( spl9_46
    | spl9_48
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | spl9_19 ),
    inference(avatar_split_clause,[],[f200,f147,f113,f105,f82,f78,f240,f237])).

fof(f82,plain,
    ( spl9_2
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f105,plain,
    ( spl9_6
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f113,plain,
    ( spl9_10
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f147,plain,
    ( spl9_19
  <=> ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f200,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f198,f148])).

fof(f148,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f147])).

fof(f198,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(resolution,[],[f128,f114])).

fof(f114,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | sK0 = X0
        | r2_hidden(k4_tarski(sK0,X0),sK2)
        | r2_hidden(k4_tarski(X0,sK0),sK2) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f127,f98])).

fof(f98,plain,
    ( v6_relat_2(sK2)
    | ~ spl9_0
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f93,f79])).

fof(f93,plain,
    ( v6_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_2 ),
    inference(resolution,[],[f83,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t42_wellord1.p',d4_wellord1)).

fof(f83,plain,
    ( v2_wellord1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | sK0 = X0
        | r2_hidden(k4_tarski(sK0,X0),sK2)
        | r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ v6_relat_2(sK2) )
    | ~ spl9_0
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f121,f79])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | sK0 = X0
        | r2_hidden(k4_tarski(sK0,X0),sK2)
        | r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ v6_relat_2(sK2) )
    | ~ spl9_6 ),
    inference(resolution,[],[f106,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t42_wellord1.p',l4_wellord1)).

fof(f106,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f184,plain,
    ( spl9_34
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f139,f113,f101,f78,f182])).

fof(f182,plain,
    ( spl9_34
  <=> r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f101,plain,
    ( spl9_4
  <=> v1_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f139,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),sK2)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f138,f102])).

fof(f102,plain,
    ( v1_relat_2(sK2)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f138,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),sK2)
    | ~ v1_relat_2(sK2)
    | ~ spl9_0
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f133,f79])).

fof(f133,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK1,sK1),sK2)
    | ~ v1_relat_2(sK2)
    | ~ spl9_10 ),
    inference(resolution,[],[f114,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,X1),X0)
      | ~ v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t42_wellord1.p',l1_wellord1)).

fof(f153,plain,(
    ~ spl9_21 ),
    inference(avatar_split_clause,[],[f73,f151])).

fof(f73,plain,(
    ~ r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_wellord1(sK2,sK0))
      | sK1 != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( ! [X3] :
                ( r2_hidden(X3,k1_wellord1(X2,X0))
               => ( X1 != X3
                  & r2_hidden(k4_tarski(X3,X1),X2) ) )
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( ! [X3] :
              ( r2_hidden(X3,k1_wellord1(X2,X0))
             => ( X1 != X3
                & r2_hidden(k4_tarski(X3,X1),X2) ) )
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t42_wellord1.p',t42_wellord1)).

fof(f149,plain,(
    ~ spl9_19 ),
    inference(avatar_split_clause,[],[f44,f147])).

fof(f44,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f115,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f43,f113])).

fof(f43,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f107,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f42,f105])).

fof(f42,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,
    ( spl9_4
    | ~ spl9_0
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f95,f82,f78,f101])).

fof(f95,plain,
    ( v1_relat_2(sK2)
    | ~ spl9_0
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f90,f79])).

fof(f90,plain,
    ( v1_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_2 ),
    inference(resolution,[],[f83,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
