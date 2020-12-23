%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t19_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:05 EDT 2019

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 110 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 ( 554 expanded)
%              Number of equality atoms :   99 ( 363 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f73,f80,f132,f163,f192])).

fof(f192,plain,
    ( spl6_3
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f177,f94])).

fof(f94,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4)) ),
    inference(unit_resulting_resolution,[],[f32,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t19_mcart_1.p',t10_mcart_1)).

fof(f32,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ( k2_mcart_1(sK0) != sK4
        & k2_mcart_1(sK0) != sK3 )
      | ( k1_mcart_1(sK0) != sK2
        & k1_mcart_1(sK0) != sK1 ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ( ( k2_mcart_1(X0) != X4
            & k2_mcart_1(X0) != X3 )
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) )
   => ( ( ( k2_mcart_1(sK0) != sK4
          & k2_mcart_1(sK0) != sK3 )
        | ( k1_mcart_1(sK0) != sK2
          & k1_mcart_1(sK0) != sK1 ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t19_mcart_1.p',t19_mcart_1)).

fof(f177,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4))
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f65,f79,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t19_mcart_1.p',d2_tarski)).

fof(f79,plain,
    ( k2_mcart_1(sK0) != sK4
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_7
  <=> k2_mcart_1(sK0) != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f65,plain,
    ( k2_mcart_1(sK0) != sK3
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_3
  <=> k2_mcart_1(sK0) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f163,plain,
    ( ~ spl6_0
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f148,f94])).

fof(f148,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4))
    | ~ spl6_0
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f65,f143,f51])).

fof(f143,plain,
    ( k2_mcart_1(sK0) != sK4
    | ~ spl6_0 ),
    inference(subsumption_resolution,[],[f35,f56])).

fof(f56,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl6_0
  <=> k1_mcart_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f35,plain,
    ( k2_mcart_1(sK0) != sK4
    | k1_mcart_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f132,plain,
    ( spl6_1
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f101,f91])).

fof(f91,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f32,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f72,f59,f51])).

fof(f59,plain,
    ( k1_mcart_1(sK0) != sK1
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_1
  <=> k1_mcart_1(sK0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f72,plain,
    ( k1_mcart_1(sK0) != sK2
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_5
  <=> k1_mcart_1(sK0) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f80,plain,
    ( ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f36,f78,f71])).

fof(f36,plain,
    ( k2_mcart_1(sK0) != sK4
    | k1_mcart_1(sK0) != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,
    ( ~ spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f34,f64,f71])).

fof(f34,plain,
    ( k2_mcart_1(sK0) != sK3
    | k1_mcart_1(sK0) != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f33,f64,f58])).

fof(f33,plain,
    ( k2_mcart_1(sK0) != sK3
    | k1_mcart_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
