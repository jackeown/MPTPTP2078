%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 133 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  165 ( 325 expanded)
%              Number of equality atoms :   56 ( 137 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f169])).

fof(f169,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f167,f53])).

fof(f53,plain,
    ( sK2 != k1_mcart_1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_1
  <=> sK2 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f167,plain,
    ( sK2 = k1_mcart_1(sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f163,f62])).

fof(f62,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_3
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f163,plain,
    ( sK1 = k1_mcart_1(sK0)
    | sK2 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f156,f43])).

fof(f43,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f22,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
       => ( r2_hidden(k2_mcart_1(X0),X3)
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f156,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(X10,k2_zfmisc_1(k2_enumset1(X12,X12,X12,X11),X13))
      | k1_mcart_1(X10) = X12
      | k1_mcart_1(X10) = X11 ) ),
    inference(resolution,[],[f152,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
      | X0 = X2
      | X0 = X1 ) ),
    inference(resolution,[],[f149,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X2))
      | X0 = X2 ) ),
    inference(condensation,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X2)) ) ),
    inference(forward_demodulation,[],[f71,f27])).

fof(f27,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k4_tarski(X0,X1)) = X2
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X2)) ) ),
    inference(resolution,[],[f45,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f32,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_enumset1(X0,X0,X0,X0))
      | ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
      | X0 = X2 ) ),
    inference(resolution,[],[f84,f75])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))
      | r2_hidden(X2,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X0,X1) != k2_enumset1(X0,X0,X0,X1)
      | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))
      | r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | r2_hidden(X2,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(superposition,[],[f47,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f35,f41,f41])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f68,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl4_2 ),
    inference(resolution,[],[f65,f43])).

fof(f65,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k2_zfmisc_1(X0,sK3))
    | spl4_2 ),
    inference(resolution,[],[f31,f57])).

fof(f57,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_2
  <=> r2_hidden(k2_mcart_1(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,
    ( ~ spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f23,f55,f60])).

fof(f23,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f24,f55,f51])).

fof(f24,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:23:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (3559)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (3560)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (3560)Refutation not found, incomplete strategy% (3560)------------------------------
% 0.22/0.53  % (3560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3559)Refutation not found, incomplete strategy% (3559)------------------------------
% 0.22/0.53  % (3559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3559)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  % (3560)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (3559)Memory used [KB]: 10618
% 0.22/0.53  
% 0.22/0.53  % (3559)Time elapsed: 0.108 s
% 0.22/0.53  % (3560)Memory used [KB]: 10618
% 0.22/0.53  % (3559)------------------------------
% 0.22/0.53  % (3559)------------------------------
% 0.22/0.53  % (3560)Time elapsed: 0.111 s
% 0.22/0.53  % (3560)------------------------------
% 0.22/0.53  % (3560)------------------------------
% 0.22/0.54  % (3577)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (3553)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (3557)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (3551)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (3549)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (3576)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (3557)Refutation not found, incomplete strategy% (3557)------------------------------
% 0.22/0.57  % (3557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (3573)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (3557)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (3557)Memory used [KB]: 10746
% 0.22/0.57  % (3557)Time elapsed: 0.124 s
% 0.22/0.57  % (3557)------------------------------
% 0.22/0.57  % (3557)------------------------------
% 0.22/0.57  % (3568)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.57  % (3571)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.58  % (3551)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % (3563)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.58  % (3566)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.55/0.59  % (3578)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.55/0.59  % SZS output start Proof for theBenchmark
% 1.55/0.59  fof(f170,plain,(
% 1.55/0.59    $false),
% 1.55/0.59    inference(avatar_sat_refutation,[],[f58,f63,f68,f169])).
% 1.55/0.59  fof(f169,plain,(
% 1.55/0.59    spl4_1 | spl4_3),
% 1.55/0.59    inference(avatar_contradiction_clause,[],[f168])).
% 1.55/0.59  fof(f168,plain,(
% 1.55/0.59    $false | (spl4_1 | spl4_3)),
% 1.55/0.59    inference(subsumption_resolution,[],[f167,f53])).
% 1.55/0.59  fof(f53,plain,(
% 1.55/0.59    sK2 != k1_mcart_1(sK0) | spl4_1),
% 1.55/0.59    inference(avatar_component_clause,[],[f51])).
% 1.55/0.59  fof(f51,plain,(
% 1.55/0.59    spl4_1 <=> sK2 = k1_mcart_1(sK0)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.55/0.59  fof(f167,plain,(
% 1.55/0.59    sK2 = k1_mcart_1(sK0) | spl4_3),
% 1.55/0.59    inference(subsumption_resolution,[],[f163,f62])).
% 1.55/0.59  fof(f62,plain,(
% 1.55/0.59    sK1 != k1_mcart_1(sK0) | spl4_3),
% 1.55/0.59    inference(avatar_component_clause,[],[f60])).
% 1.55/0.59  fof(f60,plain,(
% 1.55/0.59    spl4_3 <=> sK1 = k1_mcart_1(sK0)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.55/0.59  fof(f163,plain,(
% 1.55/0.59    sK1 = k1_mcart_1(sK0) | sK2 = k1_mcart_1(sK0)),
% 1.55/0.59    inference(resolution,[],[f156,f43])).
% 1.55/0.59  fof(f43,plain,(
% 1.55/0.59    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3))),
% 1.55/0.59    inference(definition_unfolding,[],[f22,f41])).
% 1.55/0.59  fof(f41,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.55/0.59    inference(definition_unfolding,[],[f26,f29])).
% 1.55/0.59  fof(f29,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f3])).
% 1.55/0.59  fof(f3,axiom,(
% 1.55/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.55/0.59  fof(f26,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f2])).
% 1.55/0.59  fof(f2,axiom,(
% 1.55/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.55/0.59  fof(f22,plain,(
% 1.55/0.59    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))),
% 1.55/0.59    inference(cnf_transformation,[],[f17])).
% 1.55/0.59  fof(f17,plain,(
% 1.55/0.59    (~r2_hidden(k2_mcart_1(sK0),sK3) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))),
% 1.55/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16])).
% 1.55/0.59  fof(f16,plain,(
% 1.55/0.59    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))) => ((~r2_hidden(k2_mcart_1(sK0),sK3) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f12,plain,(
% 1.55/0.59    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 1.55/0.59    inference(ennf_transformation,[],[f11])).
% 1.55/0.59  fof(f11,negated_conjecture,(
% 1.55/0.59    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.55/0.59    inference(negated_conjecture,[],[f10])).
% 1.55/0.59  fof(f10,conjecture,(
% 1.55/0.59    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).
% 1.55/0.59  fof(f156,plain,(
% 1.55/0.59    ( ! [X12,X10,X13,X11] : (~r2_hidden(X10,k2_zfmisc_1(k2_enumset1(X12,X12,X12,X11),X13)) | k1_mcart_1(X10) = X12 | k1_mcart_1(X10) = X11) )),
% 1.55/0.59    inference(resolution,[],[f152,f30])).
% 1.55/0.59  fof(f30,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f13])).
% 1.55/0.59  fof(f13,plain,(
% 1.55/0.59    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.55/0.59    inference(ennf_transformation,[],[f7])).
% 1.55/0.59  fof(f7,axiom,(
% 1.55/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.55/0.59  fof(f152,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X2 | X0 = X1) )),
% 1.55/0.59    inference(resolution,[],[f149,f75])).
% 1.55/0.59  fof(f75,plain,(
% 1.55/0.59    ( ! [X2,X0] : (~r2_hidden(X0,k2_enumset1(X2,X2,X2,X2)) | X0 = X2) )),
% 1.55/0.59    inference(condensation,[],[f74])).
% 1.55/0.59  fof(f74,plain,(
% 1.55/0.59    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X0,k2_enumset1(X2,X2,X2,X2))) )),
% 1.55/0.59    inference(forward_demodulation,[],[f71,f27])).
% 1.55/0.59  fof(f27,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.55/0.59    inference(cnf_transformation,[],[f9])).
% 1.55/0.59  fof(f9,axiom,(
% 1.55/0.59    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.55/0.59  fof(f71,plain,(
% 1.55/0.59    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X0,k2_enumset1(X2,X2,X2,X2))) )),
% 1.55/0.59    inference(resolution,[],[f45,f40])).
% 1.55/0.59  fof(f40,plain,(
% 1.55/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f21])).
% 1.55/0.59  fof(f21,plain,(
% 1.55/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.55/0.59    inference(flattening,[],[f20])).
% 1.55/0.59  fof(f20,plain,(
% 1.55/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.55/0.59    inference(nnf_transformation,[],[f4])).
% 1.55/0.59  fof(f4,axiom,(
% 1.55/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.55/0.59  fof(f45,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.55/0.59    inference(definition_unfolding,[],[f32,f42])).
% 1.55/0.59  fof(f42,plain,(
% 1.55/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.55/0.59    inference(definition_unfolding,[],[f25,f41])).
% 1.55/0.59  fof(f25,plain,(
% 1.55/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f1])).
% 1.55/0.59  fof(f1,axiom,(
% 1.55/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.55/0.59  fof(f32,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f14])).
% 1.55/0.59  fof(f14,plain,(
% 1.55/0.59    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.55/0.59    inference(ennf_transformation,[],[f8])).
% 1.55/0.59  fof(f8,axiom,(
% 1.55/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.55/0.59  fof(f149,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) | ~r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X2) )),
% 1.55/0.59    inference(resolution,[],[f84,f75])).
% 1.55/0.59  fof(f84,plain,(
% 1.55/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | ~r2_hidden(X1,k2_enumset1(X2,X2,X2,X3)) | r2_hidden(X2,k2_enumset1(X0,X0,X0,X1))) )),
% 1.55/0.59    inference(trivial_inequality_removal,[],[f83])).
% 1.55/0.59  fof(f83,plain,(
% 1.55/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X0,X1) != k2_enumset1(X0,X0,X0,X1) | ~r2_hidden(X1,k2_enumset1(X2,X2,X2,X3)) | r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | r2_hidden(X2,k2_enumset1(X0,X0,X0,X1))) )),
% 1.55/0.59    inference(superposition,[],[f47,f49])).
% 1.55/0.59  fof(f49,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.55/0.59    inference(definition_unfolding,[],[f37,f41])).
% 1.55/0.59  fof(f37,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f15])).
% 1.55/0.59  fof(f15,plain,(
% 1.55/0.59    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 1.55/0.59    inference(ennf_transformation,[],[f5])).
% 1.55/0.59  fof(f5,axiom,(
% 1.55/0.59    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 1.55/0.59  fof(f47,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 1.55/0.59    inference(definition_unfolding,[],[f35,f41,f41])).
% 1.55/0.59  fof(f35,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f19])).
% 1.55/0.59  fof(f19,plain,(
% 1.55/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.55/0.59    inference(flattening,[],[f18])).
% 1.55/0.59  fof(f18,plain,(
% 1.55/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.55/0.59    inference(nnf_transformation,[],[f6])).
% 1.55/0.59  fof(f6,axiom,(
% 1.55/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.55/0.59  fof(f68,plain,(
% 1.55/0.59    spl4_2),
% 1.55/0.59    inference(avatar_contradiction_clause,[],[f67])).
% 1.55/0.59  fof(f67,plain,(
% 1.55/0.59    $false | spl4_2),
% 1.55/0.59    inference(resolution,[],[f65,f43])).
% 1.55/0.59  fof(f65,plain,(
% 1.55/0.59    ( ! [X0] : (~r2_hidden(sK0,k2_zfmisc_1(X0,sK3))) ) | spl4_2),
% 1.55/0.59    inference(resolution,[],[f31,f57])).
% 1.55/0.59  fof(f57,plain,(
% 1.55/0.59    ~r2_hidden(k2_mcart_1(sK0),sK3) | spl4_2),
% 1.55/0.59    inference(avatar_component_clause,[],[f55])).
% 1.55/0.59  fof(f55,plain,(
% 1.55/0.59    spl4_2 <=> r2_hidden(k2_mcart_1(sK0),sK3)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.55/0.59  fof(f31,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f13])).
% 1.55/0.59  fof(f63,plain,(
% 1.55/0.59    ~spl4_3 | ~spl4_2),
% 1.55/0.59    inference(avatar_split_clause,[],[f23,f55,f60])).
% 1.55/0.59  fof(f23,plain,(
% 1.55/0.59    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK1 != k1_mcart_1(sK0)),
% 1.55/0.59    inference(cnf_transformation,[],[f17])).
% 1.55/0.59  fof(f58,plain,(
% 1.55/0.59    ~spl4_1 | ~spl4_2),
% 1.55/0.59    inference(avatar_split_clause,[],[f24,f55,f51])).
% 1.55/0.59  fof(f24,plain,(
% 1.55/0.59    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK2 != k1_mcart_1(sK0)),
% 1.55/0.59    inference(cnf_transformation,[],[f17])).
% 1.55/0.59  % SZS output end Proof for theBenchmark
% 1.55/0.59  % (3551)------------------------------
% 1.55/0.59  % (3551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (3551)Termination reason: Refutation
% 1.55/0.59  
% 1.55/0.59  % (3551)Memory used [KB]: 10874
% 1.55/0.59  % (3551)Time elapsed: 0.141 s
% 1.55/0.59  % (3551)------------------------------
% 1.55/0.59  % (3551)------------------------------
% 1.55/0.59  % (3545)Success in time 0.225 s
%------------------------------------------------------------------------------
