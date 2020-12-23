%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  37 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   53 (  82 expanded)
%              Number of equality atoms :   22 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f70])).

fof(f70,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f13,f58,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f58,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1))
    | spl3_2 ),
    inference(superposition,[],[f23,f52])).

fof(f52,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(k1_mcart_1(sK0)))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f43,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f43,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f23,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f13,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

fof(f49,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f13,f39,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
      | k2_mcart_1(X0) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,
    ( sK2 != k2_mcart_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f12,f41,f37])).

fof(f12,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:14:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (18847)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (18847)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f44,f49,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    spl3_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    $false | spl3_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f13,f58,f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ~r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1)) | spl3_2),
% 0.22/0.53    inference(superposition,[],[f23,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(k1_mcart_1(sK0))) | spl3_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f43,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    sK1 != k1_mcart_1(sK0) | spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    spl3_2 <=> sK1 = k1_mcart_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.53    inference(equality_resolution,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & k1_mcart_1(X0) = X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f7])).
% 0.22/0.53  fof(f7,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & k1_mcart_1(X0) = X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    spl3_1),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    $false | spl3_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f13,f39,f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) | k2_mcart_1(X0) = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    sK2 != k2_mcart_1(sK0) | spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    spl3_1 <=> sK2 = k2_mcart_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ~spl3_1 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f12,f41,f37])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    sK1 != k1_mcart_1(sK0) | sK2 != k2_mcart_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (18847)------------------------------
% 0.22/0.53  % (18847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18847)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (18847)Memory used [KB]: 6268
% 0.22/0.53  % (18847)Time elapsed: 0.107 s
% 0.22/0.53  % (18847)------------------------------
% 0.22/0.53  % (18847)------------------------------
% 0.22/0.54  % (18842)Success in time 0.173 s
%------------------------------------------------------------------------------
