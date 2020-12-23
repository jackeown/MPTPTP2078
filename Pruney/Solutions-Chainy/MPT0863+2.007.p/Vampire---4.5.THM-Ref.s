%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  63 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   85 ( 188 expanded)
%              Number of equality atoms :   40 ( 104 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f38,f43,f48,f49,f57,f68])).

fof(f68,plain,
    ( spl6_2
    | spl6_4
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f65,f26,f40,f31])).

fof(f31,plain,
    ( spl6_2
  <=> sK4 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f40,plain,
    ( spl6_4
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f26,plain,
    ( spl6_1
  <=> r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f65,plain,
    ( sK3 = k2_mcart_1(sK0)
    | sK4 = k2_mcart_1(sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f53,f28])).

fof(f28,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f53,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(X9,k2_zfmisc_1(X11,k2_tarski(X10,X8)))
      | k2_mcart_1(X9) = X10
      | k2_mcart_1(X9) = X8 ) ),
    inference(resolution,[],[f24,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f57,plain,
    ( spl6_5
    | spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f56,f26,f35,f45])).

fof(f45,plain,
    ( spl6_5
  <=> sK2 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f35,plain,
    ( spl6_3
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f56,plain,
    ( sK1 = k1_mcart_1(sK0)
    | sK2 = k1_mcart_1(sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f28])).

fof(f52,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X5,k2_zfmisc_1(k2_tarski(X6,X4),X7))
      | k1_mcart_1(X5) = X6
      | k1_mcart_1(X5) = X4 ) ),
    inference(resolution,[],[f24,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,
    ( ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f7,f45,f40])).

fof(f7,plain,
    ( sK2 != k1_mcart_1(sK0)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

fof(f48,plain,
    ( ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f8,f45,f31])).

fof(f8,plain,
    ( sK2 != k1_mcart_1(sK0)
    | sK4 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f43,plain,
    ( ~ spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f9,f35,f40])).

fof(f9,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,
    ( ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f10,f35,f31])).

fof(f10,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK4 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f29,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f11,f26])).

fof(f11,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (1045)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.46  % (1045)Refutation not found, incomplete strategy% (1045)------------------------------
% 0.22/0.46  % (1045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (1045)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (1045)Memory used [KB]: 1535
% 0.22/0.46  % (1045)Time elapsed: 0.053 s
% 0.22/0.46  % (1045)------------------------------
% 0.22/0.46  % (1045)------------------------------
% 0.22/0.47  % (1058)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.47  % (1058)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f29,f38,f43,f48,f49,f57,f68])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    spl6_2 | spl6_4 | ~spl6_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f65,f26,f40,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    spl6_2 <=> sK4 = k2_mcart_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    spl6_4 <=> sK3 = k2_mcart_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    spl6_1 <=> r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    sK3 = k2_mcart_1(sK0) | sK4 = k2_mcart_1(sK0) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f53,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) | ~spl6_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f26])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X10,X8,X11,X9] : (~r2_hidden(X9,k2_zfmisc_1(X11,k2_tarski(X10,X8))) | k2_mcart_1(X9) = X10 | k2_mcart_1(X9) = X8) )),
% 0.22/0.47    inference(resolution,[],[f24,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.22/0.47    inference(equality_resolution,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl6_5 | spl6_3 | ~spl6_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f56,f26,f35,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    spl6_5 <=> sK2 = k1_mcart_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl6_3 <=> sK1 = k1_mcart_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    sK1 = k1_mcart_1(sK0) | sK2 = k1_mcart_1(sK0) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f52,f28])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X6,X4,X7,X5] : (~r2_hidden(X5,k2_zfmisc_1(k2_tarski(X6,X4),X7)) | k1_mcart_1(X5) = X6 | k1_mcart_1(X5) = X4) )),
% 0.22/0.47    inference(resolution,[],[f24,f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ~spl6_4 | ~spl6_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f7,f45,f40])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    sK2 != k1_mcart_1(sK0) | sK3 != k2_mcart_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f3])).
% 0.22/0.47  fof(f3,conjecture,(
% 0.22/0.47    ! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ~spl6_2 | ~spl6_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f8,f45,f31])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    sK2 != k1_mcart_1(sK0) | sK4 != k2_mcart_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ~spl6_4 | ~spl6_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f9,f35,f40])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    sK1 != k1_mcart_1(sK0) | sK3 != k2_mcart_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ~spl6_2 | ~spl6_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f10,f35,f31])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    sK1 != k1_mcart_1(sK0) | sK4 != k2_mcart_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    spl6_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f11,f26])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (1058)------------------------------
% 0.22/0.47  % (1058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (1058)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (1058)Memory used [KB]: 6140
% 0.22/0.47  % (1058)Time elapsed: 0.057 s
% 0.22/0.47  % (1058)------------------------------
% 0.22/0.47  % (1058)------------------------------
% 0.22/0.47  % (1032)Success in time 0.111 s
%------------------------------------------------------------------------------
