%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 236 expanded)
%              Number of leaves         :   15 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  364 (1190 expanded)
%              Number of equality atoms :   60 ( 315 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f103,f122,f163,f178,f183,f191])).

fof(f191,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f189,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
      | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) )
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
          | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
        & r2_hidden(X0,k1_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
        | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) )
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f189,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f187,f30])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f187,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(resolution,[],[f177,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f177,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_6
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f183,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f181,f29])).

fof(f181,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f179,f30])).

fof(f179,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(resolution,[],[f174,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f174,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl4_5
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f178,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f171,f53,f50,f176,f173])).

fof(f50,plain,
    ( spl4_1
  <=> sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f53,plain,
    ( spl4_2
  <=> sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f171,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f170,f29])).

fof(f170,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f169,f30])).

fof(f169,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f165,f32])).

fof(f32,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f165,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_2 ),
    inference(superposition,[],[f54,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f54,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f163,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f161,f29])).

fof(f161,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f160,f30])).

fof(f160,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f159,f32])).

fof(f159,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f139,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f139,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1)
    | ~ spl4_4 ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_4
  <=> ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f122,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f120,f31])).

fof(f31,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,
    ( ~ v2_funct_1(sK1)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f119,f29])).

fof(f119,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f118,f30])).

fof(f118,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | spl4_3 ),
    inference(resolution,[],[f99,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f99,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_3
  <=> v1_funct_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f103,plain,
    ( ~ spl4_3
    | spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f96,f50,f101,f98])).

fof(f96,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ v1_funct_1(k4_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f92,f29])).

% (3338)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f92,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ v1_funct_1(k4_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1)
        | ~ v1_relat_1(sK1) )
    | spl4_1 ),
    inference(superposition,[],[f65,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_relat_1(X0),X1) = X2
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f70,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_relat_1(X0),X1) = X2
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f44,f56])).

fof(f56,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f46,f34])).

fof(f46,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,
    ( sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f64,f29])).

fof(f64,plain,
    ( sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f63,f30])).

fof(f63,plain,
    ( sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f58,f31])).

fof(f58,plain,
    ( sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(superposition,[],[f51,f41])).

fof(f51,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

% (3334)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (3323)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f55,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f33,f53,f50])).

fof(f33,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (3324)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.46  % (3328)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (3322)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (3325)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (3322)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (3320)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (3329)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (3333)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (3340)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f55,f103,f122,f163,f178,f183,f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    spl4_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    $false | spl4_6),
% 0.21/0.48    inference(subsumption_resolution,[],[f189,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    (sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & (r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.48    inference(subsumption_resolution,[],[f187,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v1_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.48    inference(resolution,[],[f177,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK1)) | spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    spl4_6 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    spl4_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f182])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    $false | spl4_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f181,f29])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f179,f30])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.48    inference(resolution,[],[f174,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ~v1_relat_1(k2_funct_1(sK1)) | spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f173])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    spl4_5 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ~spl4_5 | ~spl4_6 | ~spl4_1 | spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f171,f53,f50,f176,f173])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl4_1 <=> sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl4_2 <=> sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f170,f29])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1) | spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f30])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f165,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_2),
% 0.21/0.48    inference(superposition,[],[f54,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f53])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ~spl4_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f162])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    $false | ~spl4_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f161,f29])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f160,f30])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f159,f32])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.48    inference(resolution,[],[f139,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(equality_resolution,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1) | ~spl4_4),
% 0.21/0.48    inference(equality_resolution,[],[f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0] : (sK0 != X0 | ~r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1)) ) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl4_4 <=> ! [X0] : (sK0 != X0 | ~r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    $false | spl4_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f120,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    v2_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ~v2_funct_1(sK1) | spl4_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f119,f29])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | ~v2_funct_1(sK1) | spl4_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f30])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v2_funct_1(sK1) | spl4_3),
% 0.21/0.48    inference(resolution,[],[f99,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(superposition,[],[f40,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ~v1_funct_1(k4_relat_1(sK1)) | spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl4_3 <=> v1_funct_1(k4_relat_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ~spl4_3 | spl4_4 | spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f96,f50,f101,f98])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0] : (sK0 != X0 | ~v1_funct_1(k4_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1)) ) | spl4_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f29])).
% 0.21/0.48  % (3338)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X0] : (sK0 != X0 | ~v1_funct_1(k4_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1) | ~v1_relat_1(sK1)) ) | spl4_1),
% 0.21/0.48    inference(superposition,[],[f65,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_funct_1(k4_relat_1(X0),X1) = X2 | ~v1_funct_1(k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X1),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_funct_1(k4_relat_1(X0),X1) = X2 | ~v1_funct_1(k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X1),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f44,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f46,f34])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(rectify,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) | spl4_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f29])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f63,f30])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f58,f31])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.48    inference(superposition,[],[f51,f41])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f50])).
% 0.21/0.48  % (3334)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (3323)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ~spl4_1 | ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f53,f50])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (3322)------------------------------
% 0.21/0.48  % (3322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3322)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (3322)Memory used [KB]: 10746
% 0.21/0.48  % (3322)Time elapsed: 0.060 s
% 0.21/0.48  % (3322)------------------------------
% 0.21/0.48  % (3322)------------------------------
% 0.21/0.48  % (3317)Success in time 0.128 s
%------------------------------------------------------------------------------
