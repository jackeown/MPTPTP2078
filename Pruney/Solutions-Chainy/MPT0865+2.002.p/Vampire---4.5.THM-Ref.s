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
% DateTime   : Thu Dec  3 12:58:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  52 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   71 ( 115 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f25,f31,f38,f46,f55,f56])).

fof(f56,plain,
    ( k1_mcart_1(sK0) != sK3(sK0)
    | k2_mcart_1(sK0) != sK4(sK0)
    | sK0 != k4_tarski(sK3(sK0),sK4(sK0))
    | sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f55,plain,
    ( spl5_7
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f40,f35,f52])).

fof(f52,plain,
    ( spl5_7
  <=> k2_mcart_1(sK0) = sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f35,plain,
    ( spl5_4
  <=> sK0 = k4_tarski(sK3(sK0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f40,plain,
    ( k2_mcart_1(sK0) = sK4(sK0)
    | ~ spl5_4 ),
    inference(superposition,[],[f15,f37])).

fof(f37,plain,
    ( sK0 = k4_tarski(sK3(sK0),sK4(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f15,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f46,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f39,f35,f43])).

fof(f43,plain,
    ( spl5_5
  <=> k1_mcart_1(sK0) = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f39,plain,
    ( k1_mcart_1(sK0) = sK3(sK0)
    | ~ spl5_4 ),
    inference(superposition,[],[f14,f37])).

fof(f14,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,
    ( spl5_4
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f33,f22,f17,f35])).

fof(f17,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f22,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f33,plain,
    ( sK0 = k4_tarski(sK3(sK0),sK4(sK0))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f26,f24])).

fof(f24,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f26,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k4_tarski(sK3(X0),sK4(X0)) = X0 )
    | ~ spl5_1 ),
    inference(resolution,[],[f19,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_tarski(sK3(X1),sK4(X1)) = X1
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f19,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f31,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f10,f28])).

fof(f28,plain,
    ( spl5_3
  <=> sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f10,plain,(
    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
      & r2_hidden(X0,X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
      & r2_hidden(X0,X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,X1)
         => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f25,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f9,f22])).

fof(f9,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f20,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f8,f17])).

fof(f8,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (31109)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.44  % (31109)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f20,f25,f31,f38,f46,f55,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    k1_mcart_1(sK0) != sK3(sK0) | k2_mcart_1(sK0) != sK4(sK0) | sK0 != k4_tarski(sK3(sK0),sK4(sK0)) | sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl5_7 | ~spl5_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f40,f35,f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    spl5_7 <=> k2_mcart_1(sK0) = sK4(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    spl5_4 <=> sK0 = k4_tarski(sK3(sK0),sK4(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    k2_mcart_1(sK0) = sK4(sK0) | ~spl5_4),
% 0.21/0.44    inference(superposition,[],[f15,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    sK0 = k4_tarski(sK3(sK0),sK4(sK0)) | ~spl5_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f35])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl5_5 | ~spl5_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f39,f35,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    spl5_5 <=> k1_mcart_1(sK0) = sK3(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    k1_mcart_1(sK0) = sK3(sK0) | ~spl5_4),
% 0.21/0.44    inference(superposition,[],[f14,f37])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    spl5_4 | ~spl5_1 | ~spl5_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f33,f22,f17,f35])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    spl5_1 <=> v1_relat_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    spl5_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    sK0 = k4_tarski(sK3(sK0),sK4(sK0)) | (~spl5_1 | ~spl5_2)),
% 0.21/0.44    inference(resolution,[],[f26,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    r2_hidden(sK0,sK1) | ~spl5_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f22])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,sK1) | k4_tarski(sK3(X0),sK4(X0)) = X0) ) | ~spl5_1),
% 0.21/0.44    inference(resolution,[],[f19,f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_tarski(sK3(X1),sK4(X1)) = X1 | ~r2_hidden(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    v1_relat_1(sK1) | ~spl5_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f17])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ~spl5_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f10,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    spl5_3 <=> sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ? [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0 & r2_hidden(X0,X1) & v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f5])).
% 0.21/0.44  fof(f5,plain,(
% 0.21/0.44    ? [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0 & r2_hidden(X0,X1)) & v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.44    inference(negated_conjecture,[],[f3])).
% 0.21/0.44  fof(f3,conjecture,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    spl5_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f9,f22])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    r2_hidden(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    spl5_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f8,f17])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (31109)------------------------------
% 0.21/0.44  % (31109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (31109)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (31109)Memory used [KB]: 10618
% 0.21/0.44  % (31109)Time elapsed: 0.057 s
% 0.21/0.44  % (31109)------------------------------
% 0.21/0.44  % (31109)------------------------------
% 0.21/0.45  % (31104)Success in time 0.09 s
%------------------------------------------------------------------------------
