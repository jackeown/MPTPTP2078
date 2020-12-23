%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0913+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 153 expanded)
%              Number of leaves         :   13 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  213 ( 569 expanded)
%              Number of equality atoms :    4 (  20 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f49,f55,f64,f72,f83,f90,f94])).

fof(f94,plain,
    ( ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f92,f54])).

fof(f54,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl6_6
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f92,plain,
    ( ~ r2_hidden(sK0,sK3)
    | ~ spl6_5
    | spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f91,f48])).

fof(f48,plain,
    ( r2_hidden(sK1,sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl6_5
  <=> r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f91,plain,
    ( ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | spl6_7
    | ~ spl6_8 ),
    inference(resolution,[],[f62,f82])).

fof(f82,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_8
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f62,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_7
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f90,plain,
    ( ~ spl6_7
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f87,f81,f42,f29,f61])).

fof(f29,plain,
    ( spl6_1
  <=> r2_hidden(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f42,plain,
    ( spl6_4
  <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f87,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f86,f31])).

fof(f31,plain,
    ( r2_hidden(sK2,sK5)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f86,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | spl6_4
    | ~ spl6_8 ),
    inference(resolution,[],[f82,f43])).

fof(f43,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f83,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f21,f81])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f72,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f66,f70])).

fof(f70,plain,
    ( ~ r2_hidden(sK0,sK3)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f69,f44])).

fof(f44,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f69,plain,
    ( ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f27,f65])).

fof(f65,plain,
    ( r2_hidden(sK1,sK4)
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | r2_hidden(X1,X3) )
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl6_3
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(X1,X3)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f63,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f27,plain,
    ( ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(subsumption_resolution,[],[f22,f26])).

fof(f26,plain,(
    r2_hidden(sK2,sK5) ),
    inference(subsumption_resolution,[],[f23,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,
    ( r2_hidden(sK2,sK5)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f15,f17,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f15,plain,
    ( r2_hidden(sK2,sK5)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( ~ r2_hidden(sK2,sK5)
      | ~ r2_hidden(sK1,sK4)
      | ~ r2_hidden(sK0,sK3)
      | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) )
    & ( ( r2_hidden(sK2,sK5)
        & r2_hidden(sK1,sK4)
        & r2_hidden(sK0,sK3) )
      | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( ~ r2_hidden(X2,X5)
          | ~ r2_hidden(X1,X4)
          | ~ r2_hidden(X0,X3)
          | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
        & ( ( r2_hidden(X2,X5)
            & r2_hidden(X1,X4)
            & r2_hidden(X0,X3) )
          | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) )
   => ( ( ~ r2_hidden(sK2,sK5)
        | ~ r2_hidden(sK1,sK4)
        | ~ r2_hidden(sK0,sK3)
        | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) )
      & ( ( r2_hidden(sK2,sK5)
          & r2_hidden(sK1,sK4)
          & r2_hidden(sK0,sK3) )
        | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3)
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3)
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <~> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      <=> ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).

fof(f22,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f16,f17,f18])).

% (4665)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f16,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(resolution,[],[f63,f35])).

fof(f35,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | r2_hidden(X0,X2) )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl6_2
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f64,plain,
    ( spl6_7
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f59,f42,f34,f61])).

fof(f59,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(resolution,[],[f44,f35])).

fof(f55,plain,
    ( spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f25,f52,f42])).

fof(f25,plain,
    ( r2_hidden(sK0,sK3)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f13,f17,f18])).

fof(f13,plain,
    ( r2_hidden(sK0,sK3)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,
    ( spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f24,f46,f42])).

fof(f24,plain,
    ( r2_hidden(sK1,sK4)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f14,f17,f18])).

fof(f14,plain,
    ( r2_hidden(sK1,sK4)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f20,f38])).

fof(f36,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f26,f29])).

%------------------------------------------------------------------------------
