%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  51 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   77 ( 162 expanded)
%              Number of equality atoms :   42 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f40,f51])).

fof(f51,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f12,f47])).

% (25189)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f47,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k2_zfmisc_1(X0,k1_tarski(sK3)))
    | spl4_2 ),
    inference(forward_demodulation,[],[f42,f19])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k2_zfmisc_1(X0,k2_tarski(sK3,sK3)))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f27,f27,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f27,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl4_2
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f12,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK3 != k2_mcart_1(sK0)
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k2_mcart_1(X0) != X3
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) )
   => ( ( sK3 != k2_mcart_1(sK0)
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

fof(f40,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f35,f30,f21])).

fof(f21,plain,
    ( spl4_1
  <=> sK2 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f30,plain,
    ( spl4_3
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f35,plain,
    ( sK1 = k1_mcart_1(sK0)
    | sK2 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f15,f12])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
      | k1_mcart_1(X0) = X1
      | k1_mcart_1(X0) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f33,plain,
    ( ~ spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f13,f25,f30])).

fof(f13,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f14,f25,f21])).

fof(f14,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (25197)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (25204)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (25196)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (25196)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (25207)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f28,f33,f40,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    spl4_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    $false | spl4_2),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f12,f47])).
% 0.20/0.51  % (25189)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK0,k2_zfmisc_1(X0,k1_tarski(sK3)))) ) | spl4_2),
% 0.20/0.51    inference(forward_demodulation,[],[f42,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK0,k2_zfmisc_1(X0,k2_tarski(sK3,sK3)))) ) | spl4_2),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f27,f27,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    sK3 != k2_mcart_1(sK0) | spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    spl4_2 <=> sK3 = k2_mcart_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    (sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))) => ((sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.51    inference(negated_conjecture,[],[f5])).
% 0.20/0.51  fof(f5,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    spl4_1 | spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f35,f30,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    spl4_1 <=> sK2 = k1_mcart_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    spl4_3 <=> sK1 = k1_mcart_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    sK1 = k1_mcart_1(sK0) | sK2 = k1_mcart_1(sK0)),
% 0.20/0.51    inference(resolution,[],[f15,f12])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) | k1_mcart_1(X0) = X1 | k1_mcart_1(X0) = X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)) | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ~spl4_3 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f13,f25,f30])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ~spl4_1 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f14,f25,f21])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (25196)------------------------------
% 0.20/0.51  % (25196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25196)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (25196)Memory used [KB]: 10746
% 0.20/0.51  % (25196)Time elapsed: 0.107 s
% 0.20/0.51  % (25196)------------------------------
% 0.20/0.51  % (25196)------------------------------
% 0.20/0.51  % (25192)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (25183)Success in time 0.156 s
%------------------------------------------------------------------------------
