%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  96 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  128 ( 241 expanded)
%              Number of equality atoms :   49 ( 120 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f55,f64,f100,f249])).

fof(f249,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f128,f38,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f38,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl5_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f128,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK3,sK3,sK3))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f41,f41,f41,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f41,plain,
    ( sK1 != sK3
    | spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl5_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f100,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f54,f80,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f80,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK2,sK2,sK2))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f49,f49,f49,f32])).

fof(f49,plain,
    ( sK0 != sK2
    | spl5_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_3
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f54,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK1,sK1,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_4
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f64,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f27,f27,f57,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( sK0 != sK0
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f46,f50])).

fof(f50,plain,
    ( sK0 = sK2
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f46,plain,
    ( sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,
    ( sK1 != sK1
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f34,f42])).

fof(f42,plain,
    ( sK1 = sK3
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f34,plain,
    ( sK0 != sK2
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) ),
    inference(inner_rewriting,[],[f33])).

fof(f33,plain,
    ( sK0 != sK2
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK3,sK3))) ),
    inference(inner_rewriting,[],[f25])).

fof(f25,plain,
    ( sK0 != sK2
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f8,f19,f19])).

fof(f19,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f8,plain,
    ( sK0 != sK2
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <~> ( X1 = X3
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      <=> ( X1 = X3
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f27,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k1_enumset1(X0,X1,X4)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,
    ( spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f45,f40,f52,f48])).

fof(f45,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK1,sK1,sK1)))
    | sK0 = sK2
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f24,f42])).

fof(f24,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f9,f19,f19])).

fof(f9,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f23,f40,f36])).

fof(f23,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f10,f19,f19])).

fof(f10,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:39:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (13893)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (13893)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (13895)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (13892)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f250,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f43,f55,f64,f100,f249])).
% 0.22/0.56  fof(f249,plain,(
% 0.22/0.56    ~spl5_1 | spl5_2),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f225])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    $false | (~spl5_1 | spl5_2)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f128,f38,f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3))) | ~spl5_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    spl5_1 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    ~r2_hidden(sK1,k1_enumset1(sK3,sK3,sK3)) | spl5_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f41,f41,f41,f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.22/0.56    inference(equality_resolution,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    sK1 != sK3 | spl5_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    spl5_2 <=> sK1 = sK3),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    spl5_3 | ~spl5_4),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f98])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    $false | (spl5_3 | ~spl5_4)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f54,f80,f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ~r2_hidden(sK0,k1_enumset1(sK2,sK2,sK2)) | spl5_3),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f49,f49,f49,f32])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    sK0 != sK2 | spl5_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    spl5_3 <=> sK0 = sK2),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK1,sK1,sK1))) | ~spl5_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    spl5_4 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK1,sK1,sK1)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ~spl5_2 | ~spl5_3),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    $false | (~spl5_2 | ~spl5_3)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f27,f27,f57,f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) | (~spl5_2 | ~spl5_3)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    sK0 != sK0 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) | (~spl5_2 | ~spl5_3)),
% 0.22/0.56    inference(backward_demodulation,[],[f46,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    sK0 = sK2 | ~spl5_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f48])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) | ~spl5_2),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    sK1 != sK1 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) | ~spl5_2),
% 0.22/0.56    inference(backward_demodulation,[],[f34,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    sK1 = sK3 | ~spl5_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f40])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    sK0 != sK2 | sK1 != sK3 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))),
% 0.22/0.56    inference(inner_rewriting,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    sK0 != sK2 | sK1 != sK3 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK3,sK3)))),
% 0.22/0.56    inference(inner_rewriting,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    sK0 != sK2 | sK1 != sK3 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)))),
% 0.22/0.56    inference(definition_unfolding,[],[f8,f19,f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
% 0.22/0.56  fof(f8,plain,(
% 0.22/0.56    sK0 != sK2 | sK1 != sK3 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <~> (X1 = X3 & X0 = X2))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.22/0.56    inference(negated_conjecture,[],[f4])).
% 0.22/0.56  fof(f4,conjecture,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_enumset1(X0,X1,X4))) )),
% 0.22/0.56    inference(equality_resolution,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X0,X1,X4) != X3) )),
% 0.22/0.56    inference(equality_resolution,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    spl5_3 | spl5_4 | ~spl5_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f45,f40,f52,f48])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK1,sK1,sK1))) | sK0 = sK2 | ~spl5_2),
% 0.22/0.56    inference(backward_demodulation,[],[f24,f42])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)))),
% 0.22/0.56    inference(definition_unfolding,[],[f9,f19,f19])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    spl5_1 | spl5_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f23,f40,f36])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK3,sK3,sK3)))),
% 0.22/0.56    inference(definition_unfolding,[],[f10,f19,f19])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (13893)------------------------------
% 0.22/0.56  % (13893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (13893)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (13893)Memory used [KB]: 6396
% 0.22/0.56  % (13893)Time elapsed: 0.120 s
% 0.22/0.56  % (13893)------------------------------
% 0.22/0.56  % (13893)------------------------------
% 0.22/0.56  % (13888)Success in time 0.199 s
%------------------------------------------------------------------------------
