%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t11_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:04 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  66 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 171 expanded)
%              Number of equality atoms :   21 (  39 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f74,f82,f105,f117,f123])).

fof(f123,plain,
    ( spl10_11
    | ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl10_11
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f121,f81])).

fof(f81,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl10_11
  <=> ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f121,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl10_22 ),
    inference(resolution,[],[f116,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t11_mcart_1.p',d2_zfmisc_1)).

fof(f116,plain,
    ( sP6(sK0,sK2,sK1)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl10_22
  <=> sP6(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f117,plain,
    ( spl10_22
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f110,f103,f56,f52,f115])).

fof(f52,plain,
    ( spl10_0
  <=> r2_hidden(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f56,plain,
    ( spl10_2
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f103,plain,
    ( spl10_20
  <=> k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f110,plain,
    ( sP6(sK0,sK2,sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f109,f104])).

fof(f104,plain,
    ( k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) = sK0
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f103])).

fof(f109,plain,
    ( sP6(k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)),sK2,sK1)
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(resolution,[],[f62,f57])).

fof(f57,plain,
    ( r2_hidden(k2_mcart_1(sK0),sK2)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | sP6(k4_tarski(k1_mcart_1(sK0),X0),X1,sK1) )
    | ~ spl10_0 ),
    inference(resolution,[],[f53,f49])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | sP6(k4_tarski(X4,X5),X1,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,
    ( r2_hidden(k1_mcart_1(sK0),sK1)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f52])).

fof(f105,plain,
    ( spl10_20
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f83,f72,f103])).

fof(f72,plain,
    ( spl10_6
  <=> k4_tarski(sK3,sK4) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f83,plain,
    ( k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) = sK0
    | ~ spl10_6 ),
    inference(superposition,[],[f50,f73])).

fof(f73,plain,
    ( k4_tarski(sK3,sK4) = sK0
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f50,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) = k4_tarski(k1_mcart_1(k4_tarski(X1,X2)),k2_mcart_1(k4_tarski(X1,X2))) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t11_mcart_1.p',t8_mcart_1)).

fof(f82,plain,(
    ~ spl10_11 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(k2_mcart_1(X0),X2)
          & r2_hidden(k1_mcart_1(X0),X1) )
       => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
          | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t11_mcart_1.p',t11_mcart_1)).

fof(f74,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    k4_tarski(sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
