%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 182 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  144 ( 322 expanded)
%              Number of equality atoms :   74 ( 228 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f90,f100])).

fof(f100,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f96,f64,f59])).

fof(f59,plain,
    ( spl4_2
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f64,plain,
    ( spl4_3
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f96,plain,
    ( sK2 = k2_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f51,f48])).

fof(f48,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(definition_unfolding,[],[f23,f47,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f46])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( sK3 != k2_mcart_1(sK0)
        & sK2 != k2_mcart_1(sK0) )
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f21])).

fof(f21,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X3 ) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = X3
      | k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f90,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( sK1 != sK1
    | spl4_1 ),
    inference(superposition,[],[f57,f84])).

fof(f84,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f79,f48])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(resolution,[],[f78,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(condensation,[],[f77])).

fof(f77,plain,(
    ! [X10,X8,X11,X9] :
      ( X9 = X10
      | ~ r2_hidden(X9,k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X10))
      | ~ r2_hidden(X8,X11) ) ),
    inference(forward_demodulation,[],[f76,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f76,plain,(
    ! [X10,X8,X11,X9] :
      ( k2_mcart_1(k4_tarski(X8,X9)) = X10
      | ~ r2_hidden(X9,k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X10))
      | ~ r2_hidden(X8,X11) ) ),
    inference(resolution,[],[f49,f69])).

fof(f69,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X3,X1) ) ),
    inference(forward_demodulation,[],[f68,f28])).

fof(f28,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(forward_demodulation,[],[f53,f29])).

fof(f53,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
      | k2_mcart_1(X0) = X2 ) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f57,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_1
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f67,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f24,f64,f55])).

fof(f24,plain,
    ( sK2 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f25,f59,f55])).

fof(f25,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:33:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (6466)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (6474)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (6466)Refutation not found, incomplete strategy% (6466)------------------------------
% 0.22/0.50  % (6466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (6466)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (6466)Memory used [KB]: 6140
% 0.22/0.50  % (6466)Time elapsed: 0.086 s
% 0.22/0.50  % (6466)------------------------------
% 0.22/0.50  % (6466)------------------------------
% 0.22/0.50  % (6474)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (6488)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f62,f67,f90,f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    spl4_2 | spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f96,f64,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl4_2 <=> sK3 = k2_mcart_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    spl4_3 <=> sK2 = k2_mcart_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    sK2 = k2_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.22/0.51    inference(resolution,[],[f51,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))),
% 0.22/0.51    inference(definition_unfolding,[],[f23,f47,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f27,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f30,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f36,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f39,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f40,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f26,f46])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))) => (((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f13])).
% 0.22/0.51  fof(f13,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X3) )),
% 0.22/0.51    inference(definition_unfolding,[],[f38,f46])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2 | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl4_1),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    $false | spl4_1),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    sK1 != sK1 | spl4_1),
% 0.22/0.51    inference(superposition,[],[f57,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    sK1 = k1_mcart_1(sK0)),
% 0.22/0.51    inference(resolution,[],[f79,f48])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.22/0.51    inference(resolution,[],[f78,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 0.22/0.51    inference(condensation,[],[f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X10,X8,X11,X9] : (X9 = X10 | ~r2_hidden(X9,k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X10)) | ~r2_hidden(X8,X11)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f76,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X10,X8,X11,X9] : (k2_mcart_1(k4_tarski(X8,X9)) = X10 | ~r2_hidden(X9,k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X10)) | ~r2_hidden(X8,X11)) )),
% 0.22/0.51    inference(resolution,[],[f49,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(X4,X2) | ~r2_hidden(X3,X1)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f68,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (~r2_hidden(X4,X2) | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f53,f29])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0) | (~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) | k2_mcart_1(X0) = X2) )),
% 0.22/0.51    inference(definition_unfolding,[],[f34,f47])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_mcart_1(X0) = X2 | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    sK1 != k1_mcart_1(sK0) | spl4_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl4_1 <=> sK1 = k1_mcart_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ~spl4_1 | ~spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f64,f55])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    sK2 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ~spl4_1 | ~spl4_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f25,f59,f55])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (6474)------------------------------
% 0.22/0.51  % (6474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6474)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (6474)Memory used [KB]: 6268
% 0.22/0.51  % (6474)Time elapsed: 0.097 s
% 0.22/0.51  % (6474)------------------------------
% 0.22/0.51  % (6474)------------------------------
% 0.22/0.51  % (6461)Success in time 0.146 s
%------------------------------------------------------------------------------
