%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0855+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:46 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
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
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f38,f42,f47,f59,f65])).

fof(f65,plain,
    ( spl9_4
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f63,f41])).

fof(f41,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl9_4
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f63,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl9_6 ),
    inference(resolution,[],[f58,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f58,plain,
    ( sP6(sK0,sK2,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl9_6
  <=> sP6(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f59,plain,
    ( spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f52,f45,f30,f26,f57])).

fof(f26,plain,
    ( spl9_1
  <=> r2_hidden(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f30,plain,
    ( spl9_2
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f45,plain,
    ( spl9_5
  <=> sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f52,plain,
    ( sP6(sK0,sK2,sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f51,f46])).

fof(f46,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f51,plain,
    ( sP6(k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)),sK2,sK1)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f33,f31])).

fof(f31,plain,
    ( r2_hidden(k2_mcart_1(sK0),sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | sP6(k4_tarski(k1_mcart_1(sK0),X0),X1,sK1) )
    | ~ spl9_1 ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | sP6(k4_tarski(X4,X5),X1,X0) ) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f27,plain,
    ( r2_hidden(k1_mcart_1(sK0),sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f47,plain,
    ( spl9_5
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f43,f36,f45])).

fof(f36,plain,
    ( spl9_3
  <=> sK0 = k4_tarski(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f43,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ spl9_3 ),
    inference(superposition,[],[f24,f37])).

fof(f37,plain,
    ( sK0 = k4_tarski(sK3,sK4)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f24,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) = k4_tarski(k1_mcart_1(k4_tarski(X1,X2)),k2_mcart_1(k4_tarski(X1,X2))) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_mcart_1)).

fof(f42,plain,(
    ~ spl9_4 ),
    inference(avatar_split_clause,[],[f11,f40])).

fof(f11,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(k2_mcart_1(X0),X2)
          & r2_hidden(k1_mcart_1(X0),X1) )
       => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
          | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

fof(f38,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f10,f36])).

fof(f10,plain,(
    sK0 = k4_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f9,f30])).

fof(f9,plain,(
    r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f8,f26])).

fof(f8,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
