%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 171 expanded)
%              Number of leaves         :   15 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  375 ( 834 expanded)
%              Number of equality atoms :   57 ( 109 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f142,f148,f173,f177,f181,f205,f213])).

fof(f213,plain,
    ( spl4_1
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl4_1
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f39,f211])).

fof(f211,plain,
    ( ! [X2] : k5_relat_1(k6_relat_1(X2),sK1) = k7_relat_1(sK1,X2)
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f180,f209])).

fof(f209,plain,
    ( ! [X1] :
        ( k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1)
        | ~ r2_hidden(sK2(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1)),X1) )
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,
    ( ! [X1] :
        ( k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1)
        | ~ r2_hidden(sK2(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1)),X1)
        | k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1) )
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(resolution,[],[f206,f176])).

fof(f176,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1))),sK1)
        | k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_15
  <=> ! [X1] :
        ( k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1)
        | r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1))),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1)
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
        | ~ r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0) )
    | ~ spl4_18 ),
    inference(resolution,[],[f204,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f204,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k6_relat_1(X0))
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
        | ~ r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1)
        | ~ r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl4_18
  <=> ! [X0] :
        ( k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1)
        | ~ r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f180,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(sK1,X2,k5_relat_1(k6_relat_1(X2),sK1)),X2)
        | k5_relat_1(k6_relat_1(X2),sK1) = k7_relat_1(sK1,X2) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_16
  <=> ! [X2] :
        ( k5_relat_1(k6_relat_1(X2),sK1) = k7_relat_1(sK1,X2)
        | r2_hidden(sK2(sK1,X2,k5_relat_1(k6_relat_1(X2),sK1)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f39,plain,
    ( k7_relat_1(sK1,sK0) != k5_relat_1(k6_relat_1(sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_1
  <=> k7_relat_1(sK1,sK0) = k5_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f205,plain,
    ( ~ spl4_2
    | spl4_18
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f201,f171,f203,f42])).

fof(f42,plain,
    ( spl4_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f171,plain,
    ( spl4_14
  <=> ! [X0] :
        ( k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))
        | ~ r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0)
        | ~ r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f201,plain,
    ( ! [X0] :
        ( k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
        | ~ r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0)
        | ~ r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl4_14 ),
    inference(resolution,[],[f172,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f172,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
        | ~ r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0)
        | ~ r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f181,plain,
    ( ~ spl4_2
    | spl4_16
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f167,f146,f42,f179,f42])).

fof(f146,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
        | ~ v1_relat_1(X2)
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2)
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f167,plain,
    ( ! [X2] :
        ( k5_relat_1(k6_relat_1(X2),sK1) = k7_relat_1(sK1,X2)
        | r2_hidden(sK2(sK1,X2,k5_relat_1(k6_relat_1(X2),sK1)),X2)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(resolution,[],[f159,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

fof(f159,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),k5_relat_1(k6_relat_1(X0),sK1))
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) )
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(factoring,[],[f152])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X0),sK1))),k5_relat_1(k6_relat_1(X1),sK1))
        | k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X0),sK1)
        | r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X0),sK1))),k5_relat_1(k6_relat_1(X0),sK1)) )
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(resolution,[],[f151,f43])).

fof(f43,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f151,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(k6_relat_1(X2),X0) = k7_relat_1(sK1,X1)
        | r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X2),X0)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X2),X0))),k5_relat_1(k6_relat_1(X1),sK1))
        | r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X2),X0)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X2),X0))),k5_relat_1(k6_relat_1(X2),X0)) )
    | ~ spl4_12 ),
    inference(resolution,[],[f150,f23])).

fof(f150,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(X2)
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2)
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1))
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2)) )
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2))
        | ~ v1_relat_1(X2)
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2)
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl4_12 ),
    inference(resolution,[],[f147,f30])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2))
        | ~ v1_relat_1(X2)
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2)
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f177,plain,
    ( ~ spl4_2
    | spl4_15
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f166,f146,f42,f175,f42])).

fof(f166,plain,
    ( ! [X1] :
        ( k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1)
        | r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1))),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(resolution,[],[f159,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f173,plain,
    ( ~ spl4_2
    | spl4_14
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f169,f146,f42,f171,f42])).

fof(f169,plain,
    ( ! [X0] :
        ( k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
        | ~ r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1)
        | ~ r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( ! [X0] :
        ( k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
        | ~ r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1)
        | ~ r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0)
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(resolution,[],[f159,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK2(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
                    & r2_hidden(sK2(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
            & r2_hidden(sK2(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f148,plain,
    ( ~ spl4_2
    | spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f144,f140,f146,f42])).

% (15706)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f140,plain,
    ( spl4_11
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2))
        | ~ r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),X3)
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X3),sK1))
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f144,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2))
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1))
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_11 ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2))
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1))
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2)
        | ~ v1_relat_1(X2)
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2)
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_11 ),
    inference(resolution,[],[f141,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f141,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),X3)
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2))
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X3),sK1))
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f142,plain,
    ( ~ spl4_2
    | spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f138,f42,f140,f42])).

fof(f138,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2))
        | ~ v1_relat_1(X2)
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2)
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X3),sK1))
        | ~ r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),X3)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_2 ),
    inference(resolution,[],[f135,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),sK1)
        | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2))
        | ~ v1_relat_1(X2)
        | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f93,f43])).

fof(f93,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ v1_relat_1(X3)
      | k7_relat_1(X3,X4) = k5_relat_1(k6_relat_1(X5),X6)
      | r2_hidden(k4_tarski(sK2(X3,X4,k5_relat_1(k6_relat_1(X5),X6)),sK3(X3,X4,k5_relat_1(k6_relat_1(X5),X6))),k5_relat_1(k6_relat_1(X5),X6))
      | ~ v1_relat_1(X6)
      | r2_hidden(k4_tarski(sK2(X3,X4,k5_relat_1(k6_relat_1(X5),X6)),sK3(X3,X4,k5_relat_1(k6_relat_1(X5),X6))),X3) ) ),
    inference(resolution,[],[f47,f23])).

fof(f47,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ v1_relat_1(X7)
      | r2_hidden(k4_tarski(sK2(X5,X6,k5_relat_1(X7,X8)),sK3(X5,X6,k5_relat_1(X7,X8))),k5_relat_1(X7,X8))
      | k5_relat_1(X7,X8) = k7_relat_1(X5,X6)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X8)
      | r2_hidden(k4_tarski(sK2(X5,X6,k5_relat_1(X7,X8)),sK3(X5,X6,k5_relat_1(X7,X8))),X5) ) ),
    inference(resolution,[],[f28,f30])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k7_relat_1(sK1,sK0) != k5_relat_1(k6_relat_1(sK0),sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k5_relat_1(k6_relat_1(X0),X1)
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k5_relat_1(k6_relat_1(sK0),sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k5_relat_1(k6_relat_1(X0),X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f40,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    k7_relat_1(sK1,sK0) != k5_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (15714)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (15714)Refutation not found, incomplete strategy% (15714)------------------------------
% 0.20/0.47  % (15714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (15716)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (15714)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (15714)Memory used [KB]: 1535
% 0.20/0.47  % (15714)Time elapsed: 0.049 s
% 0.20/0.47  % (15714)------------------------------
% 0.20/0.47  % (15714)------------------------------
% 0.20/0.48  % (15701)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (15715)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (15704)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (15701)Refutation not found, incomplete strategy% (15701)------------------------------
% 0.20/0.48  % (15701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (15701)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (15701)Memory used [KB]: 10490
% 0.20/0.48  % (15701)Time elapsed: 0.060 s
% 0.20/0.48  % (15701)------------------------------
% 0.20/0.48  % (15701)------------------------------
% 0.20/0.49  % (15709)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (15705)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (15700)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (15707)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (15703)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (15711)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (15712)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (15704)Refutation not found, incomplete strategy% (15704)------------------------------
% 0.20/0.50  % (15704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15704)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15704)Memory used [KB]: 10490
% 0.20/0.50  % (15704)Time elapsed: 0.096 s
% 0.20/0.50  % (15704)------------------------------
% 0.20/0.50  % (15704)------------------------------
% 0.20/0.51  % (15718)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (15722)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (15713)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (15708)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (15722)Refutation not found, incomplete strategy% (15722)------------------------------
% 0.20/0.51  % (15722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15722)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (15722)Memory used [KB]: 10490
% 0.20/0.51  % (15722)Time elapsed: 0.095 s
% 0.20/0.51  % (15722)------------------------------
% 0.20/0.51  % (15722)------------------------------
% 0.20/0.51  % (15717)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (15720)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.52  % (15721)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.52  % (15710)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.52  % (15707)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f214,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f40,f44,f142,f148,f173,f177,f181,f205,f213])).
% 0.20/0.52  fof(f213,plain,(
% 0.20/0.52    spl4_1 | ~spl4_15 | ~spl4_16 | ~spl4_18),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f212])).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    $false | (spl4_1 | ~spl4_15 | ~spl4_16 | ~spl4_18)),
% 0.20/0.52    inference(subsumption_resolution,[],[f39,f211])).
% 0.20/0.52  fof(f211,plain,(
% 0.20/0.52    ( ! [X2] : (k5_relat_1(k6_relat_1(X2),sK1) = k7_relat_1(sK1,X2)) ) | (~spl4_15 | ~spl4_16 | ~spl4_18)),
% 0.20/0.52    inference(subsumption_resolution,[],[f180,f209])).
% 0.20/0.52  fof(f209,plain,(
% 0.20/0.52    ( ! [X1] : (k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1) | ~r2_hidden(sK2(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1)),X1)) ) | (~spl4_15 | ~spl4_18)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f208])).
% 0.20/0.52  fof(f208,plain,(
% 0.20/0.52    ( ! [X1] : (k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1) | ~r2_hidden(sK2(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1)),X1) | k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1)) ) | (~spl4_15 | ~spl4_18)),
% 0.20/0.52    inference(resolution,[],[f206,f176])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1))),sK1) | k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1)) ) | ~spl4_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f175])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    spl4_15 <=> ! [X1] : (k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1) | r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1))),sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.52  fof(f206,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) | ~r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0)) ) | ~spl4_18),
% 0.20/0.52    inference(resolution,[],[f204,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) | ~r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1) | ~r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0)) ) | ~spl4_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f203])).
% 0.20/0.52  fof(f203,plain,(
% 0.20/0.52    spl4_18 <=> ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) | ~v1_relat_1(k6_relat_1(X0)) | ~r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1) | ~r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    ( ! [X2] : (r2_hidden(sK2(sK1,X2,k5_relat_1(k6_relat_1(X2),sK1)),X2) | k5_relat_1(k6_relat_1(X2),sK1) = k7_relat_1(sK1,X2)) ) | ~spl4_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f179])).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    spl4_16 <=> ! [X2] : (k5_relat_1(k6_relat_1(X2),sK1) = k7_relat_1(sK1,X2) | r2_hidden(sK2(sK1,X2,k5_relat_1(k6_relat_1(X2),sK1)),X2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    k7_relat_1(sK1,sK0) != k5_relat_1(k6_relat_1(sK0),sK1) | spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    spl4_1 <=> k7_relat_1(sK1,sK0) = k5_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f205,plain,(
% 0.20/0.52    ~spl4_2 | spl4_18 | ~spl4_14),
% 0.20/0.52    inference(avatar_split_clause,[],[f201,f171,f203,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    spl4_2 <=> v1_relat_1(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    spl4_14 <=> ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) | ~v1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) | ~r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0) | ~r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) | ~r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0) | ~r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X0))) ) | ~spl4_14),
% 0.20/0.52    inference(resolution,[],[f172,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) | ~r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0) | ~r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1)) ) | ~spl4_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f171])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    ~spl4_2 | spl4_16 | ~spl4_2 | ~spl4_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f167,f146,f42,f179,f42])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    spl4_12 <=> ! [X1,X0,X2] : (r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(X2) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    ( ! [X2] : (k5_relat_1(k6_relat_1(X2),sK1) = k7_relat_1(sK1,X2) | r2_hidden(sK2(sK1,X2,k5_relat_1(k6_relat_1(X2),sK1)),X2) | ~v1_relat_1(sK1)) ) | (~spl4_2 | ~spl4_12)),
% 0.20/0.52    inference(resolution,[],[f159,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | r2_hidden(X0,X2) | ~v1_relat_1(X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 0.20/0.52    inference(nnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),k5_relat_1(k6_relat_1(X0),sK1)) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | (~spl4_2 | ~spl4_12)),
% 0.20/0.52    inference(factoring,[],[f152])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X0),sK1))),k5_relat_1(k6_relat_1(X1),sK1)) | k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X0),sK1) | r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X0),sK1))),k5_relat_1(k6_relat_1(X0),sK1))) ) | (~spl4_2 | ~spl4_12)),
% 0.20/0.52    inference(resolution,[],[f151,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    v1_relat_1(sK1) | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f42])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(X2),X0) = k7_relat_1(sK1,X1) | r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X2),X0)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X2),X0))),k5_relat_1(k6_relat_1(X1),sK1)) | r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X2),X0)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X2),X0))),k5_relat_1(k6_relat_1(X2),X0))) ) | ~spl4_12),
% 0.20/0.52    inference(resolution,[],[f150,f23])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X2) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1)) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2))) ) | ~spl4_12),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f149])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(X2) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1)) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X1))) ) | ~spl4_12),
% 0.20/0.52    inference(resolution,[],[f147,f30])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(X2) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1))) ) | ~spl4_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f146])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    ~spl4_2 | spl4_15 | ~spl4_2 | ~spl4_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f166,f146,f42,f175,f42])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    ( ! [X1] : (k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1) | r2_hidden(k4_tarski(sK2(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1)),sK3(sK1,X1,k5_relat_1(k6_relat_1(X1),sK1))),sK1) | ~v1_relat_1(sK1)) ) | (~spl4_2 | ~spl4_12)),
% 0.20/0.52    inference(resolution,[],[f159,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | r2_hidden(k4_tarski(X0,X1),X3) | ~v1_relat_1(X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    ~spl4_2 | spl4_14 | ~spl4_2 | ~spl4_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f169,f146,f42,f171,f42])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) | ~r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1) | ~r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0) | ~v1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) | ~v1_relat_1(sK1)) ) | (~spl4_2 | ~spl4_12)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f165])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) | ~r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1))),sK1) | ~r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X0),sK1)),X0) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) | ~v1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) | ~v1_relat_1(sK1)) ) | (~spl4_2 | ~spl4_12)),
% 0.20/0.52    inference(resolution,[],[f159,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | k7_relat_1(X0,X1) = X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) & r2_hidden(sK2(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) & r2_hidden(sK2(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(rectify,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ~spl4_2 | spl4_12 | ~spl4_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f144,f140,f146,f42])).
% 0.20/0.52  % (15706)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    spl4_11 <=> ! [X1,X3,X0,X2] : (r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2)) | ~r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),X3) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X3),sK1)) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2)) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1)) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(sK1)) ) | ~spl4_11),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f143])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2)) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),sK1)) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2) | ~v1_relat_1(X2) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(sK1)) ) | ~spl4_11),
% 0.20/0.52    inference(resolution,[],[f141,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | k7_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),X3) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2)) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X3),sK1)) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2) | ~v1_relat_1(X2)) ) | ~spl4_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f140])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    ~spl4_2 | spl4_11 | ~spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f138,f42,f140,f42])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(X2) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X3),sK1)) | ~r2_hidden(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),X3) | ~v1_relat_1(sK1)) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f135,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),X3) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(X0,X2) | ~v1_relat_1(X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),sK1) | r2_hidden(k4_tarski(sK2(sK1,X0,k5_relat_1(k6_relat_1(X1),X2)),sK3(sK1,X0,k5_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(X2) | k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X1),X2)) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f93,f43])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ( ! [X6,X4,X5,X3] : (~v1_relat_1(X3) | k7_relat_1(X3,X4) = k5_relat_1(k6_relat_1(X5),X6) | r2_hidden(k4_tarski(sK2(X3,X4,k5_relat_1(k6_relat_1(X5),X6)),sK3(X3,X4,k5_relat_1(k6_relat_1(X5),X6))),k5_relat_1(k6_relat_1(X5),X6)) | ~v1_relat_1(X6) | r2_hidden(k4_tarski(sK2(X3,X4,k5_relat_1(k6_relat_1(X5),X6)),sK3(X3,X4,k5_relat_1(k6_relat_1(X5),X6))),X3)) )),
% 0.20/0.52    inference(resolution,[],[f47,f23])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X6,X8,X7,X5] : (~v1_relat_1(X7) | r2_hidden(k4_tarski(sK2(X5,X6,k5_relat_1(X7,X8)),sK3(X5,X6,k5_relat_1(X7,X8))),k5_relat_1(X7,X8)) | k5_relat_1(X7,X8) = k7_relat_1(X5,X6) | ~v1_relat_1(X5) | ~v1_relat_1(X8) | r2_hidden(k4_tarski(sK2(X5,X6,k5_relat_1(X7,X8)),sK3(X5,X6,k5_relat_1(X7,X8))),X5)) )),
% 0.20/0.52    inference(resolution,[],[f28,f30])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | k7_relat_1(X0,X1) = X2 | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f21,f42])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    k7_relat_1(sK1,sK0) != k5_relat_1(k6_relat_1(sK0),sK1) & v1_relat_1(sK1)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0,X1] : (k7_relat_1(X1,X0) != k5_relat_1(k6_relat_1(X0),X1) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k5_relat_1(k6_relat_1(sK0),sK1) & v1_relat_1(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f7,plain,(
% 0.20/0.52    ? [X0,X1] : (k7_relat_1(X1,X0) != k5_relat_1(k6_relat_1(X0),X1) & v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.52    inference(negated_conjecture,[],[f5])).
% 0.20/0.52  fof(f5,conjecture,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ~spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f22,f38])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    k7_relat_1(sK1,sK0) != k5_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (15707)------------------------------
% 0.20/0.52  % (15707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15707)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (15707)Memory used [KB]: 10874
% 0.20/0.52  % (15707)Time elapsed: 0.083 s
% 0.20/0.52  % (15707)------------------------------
% 0.20/0.52  % (15707)------------------------------
% 0.20/0.53  % (15699)Success in time 0.166 s
%------------------------------------------------------------------------------
