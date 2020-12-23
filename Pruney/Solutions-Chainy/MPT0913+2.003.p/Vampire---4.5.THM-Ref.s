%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 133 expanded)
%              Number of leaves         :   10 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  173 ( 471 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f43,f44,f45,f53,f61,f63,f65,f66,f71])).

fof(f71,plain,
    ( ~ spl6_1
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | ~ spl6_1
    | spl6_5 ),
    inference(resolution,[],[f59,f52])).

fof(f52,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl6_5
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f59,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_1 ),
    inference(resolution,[],[f28,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f28,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl6_1
  <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f66,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | spl6_5 ),
    inference(avatar_split_clause,[],[f54,f50,f35,f31])).

fof(f31,plain,
    ( spl6_2
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f35,plain,
    ( spl6_3
  <=> r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f54,plain,
    ( ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | spl6_5 ),
    inference(resolution,[],[f52,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,
    ( spl6_3
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f56,f37])).

fof(f37,plain,
    ( ~ r2_hidden(sK1,sK4)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f56,plain,
    ( r2_hidden(sK1,sK4)
    | ~ spl6_5 ),
    inference(resolution,[],[f51,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f63,plain,
    ( spl6_2
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl6_2
    | ~ spl6_5 ),
    inference(resolution,[],[f57,f33])).

fof(f33,plain,
    ( ~ r2_hidden(sK0,sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f57,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f51,f19])).

fof(f61,plain,
    ( ~ spl6_1
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | ~ spl6_1
    | spl6_4 ),
    inference(resolution,[],[f58,f41])).

fof(f41,plain,
    ( ~ r2_hidden(sK2,sK5)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl6_4
  <=> r2_hidden(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f58,plain,
    ( r2_hidden(sK2,sK5)
    | ~ spl6_1 ),
    inference(resolution,[],[f28,f20])).

fof(f53,plain,
    ( ~ spl6_5
    | ~ spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f46,f27,f39,f50])).

fof(f46,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | spl6_1 ),
    inference(resolution,[],[f21,f29])).

fof(f29,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f45,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f25,f31,f27])).

fof(f25,plain,
    ( r2_hidden(sK0,sK3)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f13,f17,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f13,plain,
    ( r2_hidden(sK0,sK3)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).

fof(f44,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f24,f35,f27])).

fof(f24,plain,
    ( r2_hidden(sK1,sK4)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f14,f17,f18])).

fof(f14,plain,
    ( r2_hidden(sK1,sK4)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,
    ( spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f23,f39,f27])).

fof(f23,plain,
    ( r2_hidden(sK2,sK5)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f15,f17,f18])).

fof(f15,plain,
    ( r2_hidden(sK2,sK5)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f22,f39,f35,f31,f27])).

fof(f22,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f16,f17,f18])).

fof(f16,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:16:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (17037)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (17037)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f42,f43,f44,f45,f53,f61,f63,f65,f66,f71])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ~spl6_1 | spl6_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    $false | (~spl6_1 | spl6_5)),
% 0.20/0.46    inference(resolution,[],[f59,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | spl6_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    spl6_5 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~spl6_1),
% 0.20/0.46    inference(resolution,[],[f28,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.46    inference(flattening,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.46    inference(nnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl6_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    spl6_1 <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ~spl6_2 | ~spl6_3 | spl6_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f54,f50,f35,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    spl6_2 <=> r2_hidden(sK0,sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    spl6_3 <=> r2_hidden(sK1,sK4)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | spl6_5),
% 0.20/0.46    inference(resolution,[],[f52,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl6_3 | ~spl6_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    $false | (spl6_3 | ~spl6_5)),
% 0.20/0.46    inference(resolution,[],[f56,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ~r2_hidden(sK1,sK4) | spl6_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f35])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    r2_hidden(sK1,sK4) | ~spl6_5),
% 0.20/0.46    inference(resolution,[],[f51,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~spl6_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f50])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    spl6_2 | ~spl6_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    $false | (spl6_2 | ~spl6_5)),
% 0.20/0.46    inference(resolution,[],[f57,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ~r2_hidden(sK0,sK3) | spl6_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f31])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    r2_hidden(sK0,sK3) | ~spl6_5),
% 0.20/0.46    inference(resolution,[],[f51,f19])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ~spl6_1 | spl6_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    $false | (~spl6_1 | spl6_4)),
% 0.20/0.46    inference(resolution,[],[f58,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ~r2_hidden(sK2,sK5) | spl6_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl6_4 <=> r2_hidden(sK2,sK5)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    r2_hidden(sK2,sK5) | ~spl6_1),
% 0.20/0.46    inference(resolution,[],[f28,f20])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ~spl6_5 | ~spl6_4 | spl6_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f46,f27,f39,f50])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ~r2_hidden(sK2,sK5) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | spl6_1),
% 0.20/0.46    inference(resolution,[],[f21,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | spl6_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f27])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl6_1 | spl6_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f31,f27])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    r2_hidden(sK0,sK3) | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.46    inference(definition_unfolding,[],[f13,f17,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    r2_hidden(sK0,sK3) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    (~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))) & ((r2_hidden(sK2,sK5) & r2_hidden(sK1,sK4) & r2_hidden(sK0,sK3)) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3,X4,X5] : ((~r2_hidden(X2,X5) | ~r2_hidden(X1,X4) | ~r2_hidden(X0,X3) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) & ((r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)) | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)))) => ((~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))) & ((r2_hidden(sK2,sK5) & r2_hidden(sK1,sK4) & r2_hidden(sK0,sK3)) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3,X4,X5] : ((~r2_hidden(X2,X5) | ~r2_hidden(X1,X4) | ~r2_hidden(X0,X3) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) & ((r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)) | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))))),
% 0.20/0.46    inference(flattening,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3,X4,X5] : (((~r2_hidden(X2,X5) | ~r2_hidden(X1,X4) | ~r2_hidden(X0,X3)) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) & ((r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)) | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))))),
% 0.20/0.46    inference(nnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3,X4,X5] : (r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) <~> (r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2,X3,X4,X5] : (r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) <=> (r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)))),
% 0.20/0.46    inference(negated_conjecture,[],[f4])).
% 0.20/0.46  fof(f4,conjecture,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5] : (r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) <=> (r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    spl6_1 | spl6_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f35,f27])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    r2_hidden(sK1,sK4) | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.46    inference(definition_unfolding,[],[f14,f17,f18])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    r2_hidden(sK1,sK4) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    spl6_1 | spl6_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f39,f27])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    r2_hidden(sK2,sK5) | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.46    inference(definition_unfolding,[],[f15,f17,f18])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    r2_hidden(sK2,sK5) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f39,f35,f31,f27])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.46    inference(definition_unfolding,[],[f16,f17,f18])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (17037)------------------------------
% 0.20/0.46  % (17037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (17037)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (17037)Memory used [KB]: 6140
% 0.20/0.46  % (17037)Time elapsed: 0.008 s
% 0.20/0.46  % (17037)------------------------------
% 0.20/0.46  % (17037)------------------------------
% 0.20/0.46  % (17032)Success in time 0.103 s
%------------------------------------------------------------------------------
