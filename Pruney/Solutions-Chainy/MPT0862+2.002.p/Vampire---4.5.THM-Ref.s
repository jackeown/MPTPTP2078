%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:26 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 101 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  205 ( 315 expanded)
%              Number of equality atoms :  137 ( 223 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f106])).

fof(f106,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f104,f65])).

fof(f65,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_2
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f104,plain,
    ( sK3 = k2_mcart_1(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f103,f70])).

fof(f70,plain,
    ( sK2 != k2_mcart_1(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_3
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f103,plain,
    ( sK2 = k2_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( sK2 = k2_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0)
    | sK2 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(definition_unfolding,[],[f20,f39,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f38])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ( sK3 != k2_mcart_1(sK0)
        & sK2 != k2_mcart_1(sK0) )
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) )
   => ( ( ( sK3 != k2_mcart_1(sK0)
          & sK2 != k2_mcart_1(sK0) )
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_mcart_1)).

fof(f83,plain,(
    ! [X14,X17,X15,X18,X16] :
      ( ~ r2_hidden(X15,k2_zfmisc_1(X18,k2_enumset1(X16,X16,X14,X17)))
      | k2_mcart_1(X15) = X16
      | k2_mcart_1(X15) = X17
      | k2_mcart_1(X15) = X14 ) ),
    inference(resolution,[],[f57,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f57,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f30,f25])).

fof(f30,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f76,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f74,f61])).

fof(f61,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_1
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f74,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f42,f40])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f28,f39])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f71,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f21,f68,f59])).

fof(f21,plain,
    ( sK2 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f22,f63,f59])).

fof(f22,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.35  % Computer   : n007.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 13:26:36 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.21/0.52  % (30347)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (30348)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.52  % (30335)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.53  % (30337)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.53  % (30337)Refutation found. Thanks to Tanya!
% 1.27/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.53  % SZS output start Proof for theBenchmark
% 1.27/0.53  fof(f107,plain,(
% 1.27/0.53    $false),
% 1.27/0.53    inference(avatar_sat_refutation,[],[f66,f71,f76,f106])).
% 1.27/0.53  fof(f106,plain,(
% 1.27/0.53    spl5_2 | spl5_3),
% 1.27/0.53    inference(avatar_contradiction_clause,[],[f105])).
% 1.27/0.53  fof(f105,plain,(
% 1.27/0.53    $false | (spl5_2 | spl5_3)),
% 1.27/0.53    inference(subsumption_resolution,[],[f104,f65])).
% 1.27/0.53  fof(f65,plain,(
% 1.27/0.53    sK3 != k2_mcart_1(sK0) | spl5_2),
% 1.27/0.53    inference(avatar_component_clause,[],[f63])).
% 1.27/0.53  fof(f63,plain,(
% 1.27/0.53    spl5_2 <=> sK3 = k2_mcart_1(sK0)),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.27/0.53  fof(f104,plain,(
% 1.27/0.53    sK3 = k2_mcart_1(sK0) | spl5_3),
% 1.27/0.53    inference(subsumption_resolution,[],[f103,f70])).
% 1.27/0.53  fof(f70,plain,(
% 1.27/0.53    sK2 != k2_mcart_1(sK0) | spl5_3),
% 1.27/0.53    inference(avatar_component_clause,[],[f68])).
% 1.27/0.53  fof(f68,plain,(
% 1.27/0.53    spl5_3 <=> sK2 = k2_mcart_1(sK0)),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.27/0.53  fof(f103,plain,(
% 1.27/0.53    sK2 = k2_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 1.27/0.53    inference(duplicate_literal_removal,[],[f102])).
% 1.27/0.53  fof(f102,plain,(
% 1.27/0.53    sK2 = k2_mcart_1(sK0) | sK3 = k2_mcart_1(sK0) | sK2 = k2_mcart_1(sK0)),
% 1.27/0.53    inference(resolution,[],[f83,f40])).
% 1.27/0.53  fof(f40,plain,(
% 1.27/0.53    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)))),
% 1.27/0.53    inference(definition_unfolding,[],[f20,f39,f38])).
% 1.27/0.53  fof(f38,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.27/0.53    inference(definition_unfolding,[],[f24,f25])).
% 1.27/0.53  fof(f25,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f4])).
% 1.27/0.53  fof(f4,axiom,(
% 1.27/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.27/0.53  fof(f24,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f3])).
% 1.27/0.53  fof(f3,axiom,(
% 1.27/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.27/0.53  fof(f39,plain,(
% 1.27/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.27/0.53    inference(definition_unfolding,[],[f23,f38])).
% 1.27/0.53  fof(f23,plain,(
% 1.27/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f2])).
% 1.27/0.53  fof(f2,axiom,(
% 1.27/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.27/0.53  fof(f20,plain,(
% 1.27/0.53    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 1.27/0.53    inference(cnf_transformation,[],[f14])).
% 1.27/0.53  fof(f14,plain,(
% 1.27/0.53    ((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f13])).
% 1.27/0.53  fof(f13,plain,(
% 1.27/0.53    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))) => (((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f9,plain,(
% 1.27/0.53    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))))),
% 1.27/0.53    inference(ennf_transformation,[],[f8])).
% 1.27/0.53  fof(f8,negated_conjecture,(
% 1.27/0.53    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 1.27/0.53    inference(negated_conjecture,[],[f7])).
% 1.27/0.53  fof(f7,conjecture,(
% 1.27/0.53    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_mcart_1)).
% 1.27/0.53  fof(f83,plain,(
% 1.27/0.53    ( ! [X14,X17,X15,X18,X16] : (~r2_hidden(X15,k2_zfmisc_1(X18,k2_enumset1(X16,X16,X14,X17))) | k2_mcart_1(X15) = X16 | k2_mcart_1(X15) = X17 | k2_mcart_1(X15) = X14) )),
% 1.27/0.53    inference(resolution,[],[f57,f27])).
% 1.27/0.53  fof(f27,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.27/0.53    inference(cnf_transformation,[],[f10])).
% 1.27/0.53  fof(f10,plain,(
% 1.27/0.53    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.27/0.53    inference(ennf_transformation,[],[f5])).
% 1.27/0.53  fof(f5,axiom,(
% 1.27/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.27/0.53  fof(f57,plain,(
% 1.27/0.53    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.27/0.53    inference(equality_resolution,[],[f50])).
% 1.27/0.53  fof(f50,plain,(
% 1.27/0.53    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.27/0.53    inference(definition_unfolding,[],[f30,f25])).
% 1.27/0.53  fof(f30,plain,(
% 1.27/0.53    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.27/0.53    inference(cnf_transformation,[],[f19])).
% 1.27/0.53  fof(f19,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).
% 1.27/0.53  fof(f18,plain,(
% 1.27/0.53    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f17,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.27/0.53    inference(rectify,[],[f16])).
% 1.27/0.53  fof(f16,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.27/0.53    inference(flattening,[],[f15])).
% 1.27/0.53  fof(f15,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.27/0.53    inference(nnf_transformation,[],[f12])).
% 1.27/0.53  fof(f12,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.27/0.53    inference(ennf_transformation,[],[f1])).
% 1.27/0.53  fof(f1,axiom,(
% 1.27/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.27/0.53  fof(f76,plain,(
% 1.27/0.53    spl5_1),
% 1.27/0.53    inference(avatar_contradiction_clause,[],[f75])).
% 1.27/0.53  fof(f75,plain,(
% 1.27/0.53    $false | spl5_1),
% 1.27/0.53    inference(subsumption_resolution,[],[f74,f61])).
% 1.27/0.53  fof(f61,plain,(
% 1.27/0.53    sK1 != k1_mcart_1(sK0) | spl5_1),
% 1.27/0.53    inference(avatar_component_clause,[],[f59])).
% 1.27/0.53  fof(f59,plain,(
% 1.27/0.53    spl5_1 <=> sK1 = k1_mcart_1(sK0)),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.27/0.53  fof(f74,plain,(
% 1.27/0.53    sK1 = k1_mcart_1(sK0)),
% 1.27/0.53    inference(resolution,[],[f42,f40])).
% 1.27/0.53  fof(f42,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.27/0.53    inference(definition_unfolding,[],[f28,f39])).
% 1.27/0.53  fof(f28,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 1.27/0.53    inference(cnf_transformation,[],[f11])).
% 1.27/0.53  fof(f11,plain,(
% 1.27/0.53    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.27/0.53    inference(ennf_transformation,[],[f6])).
% 1.27/0.53  fof(f6,axiom,(
% 1.27/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.27/0.53  fof(f71,plain,(
% 1.27/0.53    ~spl5_1 | ~spl5_3),
% 1.27/0.53    inference(avatar_split_clause,[],[f21,f68,f59])).
% 1.27/0.53  fof(f21,plain,(
% 1.27/0.53    sK2 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 1.27/0.53    inference(cnf_transformation,[],[f14])).
% 1.27/0.53  fof(f66,plain,(
% 1.27/0.53    ~spl5_1 | ~spl5_2),
% 1.27/0.53    inference(avatar_split_clause,[],[f22,f63,f59])).
% 1.27/0.53  fof(f22,plain,(
% 1.27/0.53    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 1.27/0.53    inference(cnf_transformation,[],[f14])).
% 1.27/0.53  % SZS output end Proof for theBenchmark
% 1.27/0.53  % (30337)------------------------------
% 1.27/0.53  % (30337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (30337)Termination reason: Refutation
% 1.27/0.53  
% 1.27/0.53  % (30337)Memory used [KB]: 10746
% 1.27/0.53  % (30337)Time elapsed: 0.116 s
% 1.27/0.53  % (30337)------------------------------
% 1.27/0.53  % (30337)------------------------------
% 1.27/0.53  % (30351)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.53  % (30336)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.53  % (30343)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.53  % (30338)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.53  % (30334)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.54  % (30340)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.54  % (30357)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.54  % (30353)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.27/0.54  % (30339)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.54  % (30359)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.54  % (30349)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (30360)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (30345)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.55  % (30357)Refutation not found, incomplete strategy% (30357)------------------------------
% 1.42/0.55  % (30357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (30356)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.55  % (30333)Success in time 0.182 s
%------------------------------------------------------------------------------
