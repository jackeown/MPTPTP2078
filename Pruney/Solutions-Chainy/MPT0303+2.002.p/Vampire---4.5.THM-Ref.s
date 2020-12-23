%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  64 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 154 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f45,f54,f77])).

fof(f77,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f76,f27,f51])).

% (14791)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f51,plain,
    ( spl3_4
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f27,plain,
    ( spl3_2
  <=> k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f76,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f71,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f71,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(X1,sK0),sK1)
        | r1_tarski(X1,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f68,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f68,plain,
    ( ! [X6] :
        ( r2_hidden(X6,sK0)
        | ~ r2_hidden(X6,sK1) )
    | ~ spl3_2 ),
    inference(condensation,[],[f67])).

fof(f67,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK1)
        | ~ r2_hidden(X7,sK1)
        | r2_hidden(X6,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f17])).

fof(f17,plain,(
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

fof(f33,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK0))
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(X4,sK1) )
    | ~ spl3_2 ),
    inference(superposition,[],[f18,f29])).

fof(f29,plain,
    ( k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f46,f42,f51,f22])).

fof(f22,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f46,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ spl3_3 ),
    inference(resolution,[],[f44,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f44,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f45,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f40,f27,f42])).

fof(f40,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f38])).

fof(f38,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f37,f14])).

fof(f37,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK1),sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f36,f15])).

fof(f36,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_2 ),
    inference(condensation,[],[f34])).

fof(f34,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f31,f18])).

fof(f31,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl3_2 ),
    inference(superposition,[],[f16,f29])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f8,f27])).

fof(f8,plain,(
    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(f25,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f9,f22])).

fof(f9,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (14800)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (14806)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (14798)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (14784)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (14788)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (14788)Refutation not found, incomplete strategy% (14788)------------------------------
% 0.20/0.51  % (14788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14788)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14788)Memory used [KB]: 6140
% 0.20/0.51  % (14788)Time elapsed: 0.100 s
% 0.20/0.51  % (14788)------------------------------
% 0.20/0.51  % (14788)------------------------------
% 0.20/0.51  % (14789)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (14786)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (14808)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (14806)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f25,f30,f45,f54,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    spl3_4 | ~spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f76,f27,f51])).
% 0.20/0.52  % (14791)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    spl3_4 <=> r1_tarski(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    spl3_2 <=> k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    r1_tarski(sK1,sK0) | ~spl3_2),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl3_2),
% 0.20/0.52    inference(resolution,[],[f71,f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(sK2(X1,sK0),sK1) | r1_tarski(X1,sK0)) ) | ~spl3_2),
% 0.20/0.52    inference(resolution,[],[f68,f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X6] : (r2_hidden(X6,sK0) | ~r2_hidden(X6,sK1)) ) | ~spl3_2),
% 0.20/0.52    inference(condensation,[],[f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X6,X7] : (~r2_hidden(X6,sK1) | ~r2_hidden(X7,sK1) | r2_hidden(X6,sK0)) ) | ~spl3_2),
% 0.20/0.52    inference(resolution,[],[f33,f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK0)) | ~r2_hidden(X5,sK1) | ~r2_hidden(X4,sK1)) ) | ~spl3_2),
% 0.20/0.52    inference(superposition,[],[f18,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) | ~spl3_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f27])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    spl3_1 | ~spl3_4 | ~spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f46,f42,f51,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    spl3_1 <=> sK0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~spl3_3),
% 0.20/0.52    inference(resolution,[],[f44,f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f42])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    spl3_3 | ~spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f40,f27,f42])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.52    inference(resolution,[],[f37,f14])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK2(X0,sK1),sK0) | r1_tarski(X0,sK1)) ) | ~spl3_2),
% 0.20/0.52    inference(resolution,[],[f36,f15])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl3_2),
% 0.20/0.52    inference(condensation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK0)) ) | ~spl3_2),
% 0.20/0.52    inference(resolution,[],[f31,f18])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0)) | r2_hidden(X0,sK1)) ) | ~spl3_2),
% 0.20/0.52    inference(superposition,[],[f16,f29])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f8,f27])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,plain,(
% 0.20/0.52    ? [X0,X1] : (X0 != X1 & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 0.20/0.52    inference(negated_conjecture,[],[f4])).
% 0.20/0.52  fof(f4,conjecture,(
% 0.20/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ~spl3_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f9,f22])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    sK0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (14806)------------------------------
% 0.20/0.52  % (14806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14806)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (14806)Memory used [KB]: 10746
% 0.20/0.52  % (14806)Time elapsed: 0.057 s
% 0.20/0.52  % (14806)------------------------------
% 0.20/0.52  % (14806)------------------------------
% 0.20/0.52  % (14787)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (14783)Success in time 0.159 s
%------------------------------------------------------------------------------
