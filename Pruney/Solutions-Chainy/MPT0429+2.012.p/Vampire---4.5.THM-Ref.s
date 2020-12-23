%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:45 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f18,f26,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f26,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f25,plain,(
    ~ r1_tarski(k2_tarski(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f20,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f20,plain,(
    ~ m1_subset_1(k2_tarski(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(definition_unfolding,[],[f9,f19])).

fof(f9,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

fof(f18,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (819691521)
% 0.13/0.37  ipcrm: permission denied for id (819724290)
% 0.13/0.37  ipcrm: permission denied for id (823361539)
% 0.20/0.37  ipcrm: permission denied for id (819789829)
% 0.20/0.37  ipcrm: permission denied for id (819822598)
% 0.20/0.37  ipcrm: permission denied for id (823427079)
% 0.20/0.37  ipcrm: permission denied for id (819855368)
% 0.20/0.38  ipcrm: permission denied for id (819888138)
% 0.20/0.38  ipcrm: permission denied for id (819920907)
% 0.20/0.38  ipcrm: permission denied for id (819986445)
% 0.20/0.38  ipcrm: permission denied for id (820019214)
% 0.20/0.38  ipcrm: permission denied for id (820084752)
% 0.20/0.38  ipcrm: permission denied for id (823558161)
% 0.20/0.39  ipcrm: permission denied for id (823590930)
% 0.20/0.39  ipcrm: permission denied for id (820150292)
% 0.20/0.39  ipcrm: permission denied for id (820183061)
% 0.20/0.39  ipcrm: permission denied for id (823656470)
% 0.20/0.39  ipcrm: permission denied for id (820215831)
% 0.20/0.39  ipcrm: permission denied for id (820248600)
% 0.20/0.39  ipcrm: permission denied for id (820281369)
% 0.20/0.40  ipcrm: permission denied for id (820346907)
% 0.20/0.40  ipcrm: permission denied for id (820412445)
% 0.20/0.40  ipcrm: permission denied for id (820510752)
% 0.20/0.40  ipcrm: permission denied for id (820543521)
% 0.20/0.40  ipcrm: permission denied for id (823820322)
% 0.20/0.40  ipcrm: permission denied for id (820609059)
% 0.20/0.41  ipcrm: permission denied for id (820641828)
% 0.20/0.41  ipcrm: permission denied for id (823853093)
% 0.20/0.41  ipcrm: permission denied for id (820707366)
% 0.20/0.41  ipcrm: permission denied for id (820772904)
% 0.20/0.41  ipcrm: permission denied for id (820805673)
% 0.20/0.41  ipcrm: permission denied for id (823951403)
% 0.20/0.42  ipcrm: permission denied for id (820871212)
% 0.20/0.42  ipcrm: permission denied for id (823984173)
% 0.20/0.42  ipcrm: permission denied for id (820936750)
% 0.20/0.42  ipcrm: permission denied for id (821002288)
% 0.20/0.42  ipcrm: permission denied for id (824049713)
% 0.20/0.42  ipcrm: permission denied for id (821035058)
% 0.20/0.42  ipcrm: permission denied for id (821067827)
% 0.20/0.42  ipcrm: permission denied for id (821133364)
% 0.20/0.43  ipcrm: permission denied for id (821166133)
% 0.20/0.43  ipcrm: permission denied for id (821231671)
% 0.20/0.43  ipcrm: permission denied for id (821264440)
% 0.20/0.43  ipcrm: permission denied for id (821297209)
% 0.20/0.43  ipcrm: permission denied for id (821329978)
% 0.20/0.43  ipcrm: permission denied for id (821395516)
% 0.20/0.43  ipcrm: permission denied for id (824148029)
% 0.20/0.44  ipcrm: permission denied for id (824180798)
% 0.20/0.44  ipcrm: permission denied for id (824246336)
% 0.20/0.44  ipcrm: permission denied for id (824279105)
% 0.20/0.44  ipcrm: permission denied for id (824311874)
% 0.20/0.44  ipcrm: permission denied for id (821624899)
% 0.20/0.44  ipcrm: permission denied for id (821657668)
% 0.20/0.44  ipcrm: permission denied for id (824377413)
% 0.20/0.45  ipcrm: permission denied for id (821690438)
% 0.20/0.45  ipcrm: permission denied for id (824410183)
% 0.20/0.45  ipcrm: permission denied for id (821755976)
% 0.20/0.45  ipcrm: permission denied for id (821788745)
% 0.20/0.45  ipcrm: permission denied for id (821821514)
% 0.20/0.45  ipcrm: permission denied for id (824475724)
% 0.20/0.45  ipcrm: permission denied for id (824541262)
% 0.20/0.46  ipcrm: permission denied for id (821952592)
% 0.20/0.46  ipcrm: permission denied for id (821985361)
% 0.20/0.46  ipcrm: permission denied for id (822018130)
% 0.20/0.46  ipcrm: permission denied for id (824606803)
% 0.20/0.46  ipcrm: permission denied for id (824705109)
% 0.20/0.46  ipcrm: permission denied for id (824737878)
% 0.20/0.47  ipcrm: permission denied for id (822149207)
% 0.20/0.47  ipcrm: permission denied for id (822214744)
% 0.20/0.47  ipcrm: permission denied for id (822247513)
% 0.20/0.47  ipcrm: permission denied for id (822280282)
% 0.20/0.47  ipcrm: permission denied for id (822313052)
% 0.20/0.47  ipcrm: permission denied for id (822345821)
% 0.20/0.48  ipcrm: permission denied for id (824836191)
% 0.20/0.48  ipcrm: permission denied for id (824901729)
% 0.20/0.48  ipcrm: permission denied for id (822542435)
% 0.20/0.48  ipcrm: permission denied for id (822607973)
% 0.20/0.48  ipcrm: permission denied for id (822640742)
% 0.20/0.48  ipcrm: permission denied for id (825000039)
% 0.20/0.49  ipcrm: permission denied for id (822673512)
% 0.20/0.49  ipcrm: permission denied for id (825032809)
% 0.20/0.49  ipcrm: permission denied for id (822771820)
% 0.20/0.49  ipcrm: permission denied for id (825131117)
% 0.20/0.49  ipcrm: permission denied for id (822837358)
% 0.20/0.49  ipcrm: permission denied for id (822870128)
% 0.20/0.50  ipcrm: permission denied for id (822902897)
% 0.20/0.50  ipcrm: permission denied for id (825196658)
% 0.20/0.50  ipcrm: permission denied for id (822935667)
% 0.20/0.50  ipcrm: permission denied for id (823001205)
% 0.20/0.50  ipcrm: permission denied for id (825262198)
% 0.20/0.50  ipcrm: permission denied for id (823066743)
% 0.20/0.50  ipcrm: permission denied for id (825294968)
% 0.20/0.50  ipcrm: permission denied for id (823132281)
% 0.20/0.51  ipcrm: permission denied for id (825327738)
% 0.20/0.51  ipcrm: permission denied for id (825360507)
% 0.20/0.51  ipcrm: permission denied for id (823296127)
% 0.76/0.65  % (4351)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.76/0.66  % (4343)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.76/0.66  % (4335)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.76/0.66  % (4335)Refutation found. Thanks to Tanya!
% 0.76/0.66  % SZS status Theorem for theBenchmark
% 0.76/0.66  % SZS output start Proof for theBenchmark
% 0.76/0.66  fof(f30,plain,(
% 0.76/0.66    $false),
% 0.76/0.66    inference(unit_resulting_resolution,[],[f18,f26,f24])).
% 0.76/0.66  fof(f24,plain,(
% 0.76/0.66    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.76/0.66    inference(equality_resolution,[],[f12])).
% 0.76/0.66  fof(f12,plain,(
% 0.76/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.76/0.66    inference(cnf_transformation,[],[f3])).
% 0.76/0.66  fof(f3,axiom,(
% 0.76/0.66    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.76/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.76/0.66  fof(f26,plain,(
% 0.76/0.66    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.76/0.66    inference(unit_resulting_resolution,[],[f25,f22])).
% 0.76/0.66  fof(f22,plain,(
% 0.76/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1)) )),
% 0.76/0.66    inference(definition_unfolding,[],[f16,f19])).
% 0.76/0.66  fof(f19,plain,(
% 0.76/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.76/0.66    inference(cnf_transformation,[],[f2])).
% 0.76/0.66  fof(f2,axiom,(
% 0.76/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.76/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.76/0.66  fof(f16,plain,(
% 0.76/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.76/0.66    inference(cnf_transformation,[],[f4])).
% 0.76/0.66  fof(f4,axiom,(
% 0.76/0.66    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.76/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.76/0.66  fof(f25,plain,(
% 0.76/0.66    ~r1_tarski(k2_tarski(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(sK0))),
% 0.76/0.66    inference(unit_resulting_resolution,[],[f20,f10])).
% 0.76/0.66  fof(f10,plain,(
% 0.76/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.76/0.66    inference(cnf_transformation,[],[f5])).
% 0.76/0.66  fof(f5,axiom,(
% 0.76/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.76/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.76/0.66  fof(f20,plain,(
% 0.76/0.66    ~m1_subset_1(k2_tarski(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.76/0.66    inference(definition_unfolding,[],[f9,f19])).
% 0.76/0.66  fof(f9,plain,(
% 0.76/0.66    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.76/0.66    inference(cnf_transformation,[],[f8])).
% 0.76/0.66  fof(f8,plain,(
% 0.76/0.66    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.76/0.66    inference(ennf_transformation,[],[f7])).
% 0.76/0.66  fof(f7,negated_conjecture,(
% 0.76/0.66    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.76/0.66    inference(negated_conjecture,[],[f6])).
% 0.76/0.66  fof(f6,conjecture,(
% 0.76/0.66    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.76/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.76/0.66  fof(f18,plain,(
% 0.76/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.76/0.66    inference(cnf_transformation,[],[f1])).
% 0.76/0.66  fof(f1,axiom,(
% 0.76/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.76/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.76/0.66  % SZS output end Proof for theBenchmark
% 0.76/0.66  % (4335)------------------------------
% 0.76/0.66  % (4335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.76/0.66  % (4335)Termination reason: Refutation
% 0.76/0.66  
% 0.76/0.66  % (4335)Memory used [KB]: 6140
% 0.76/0.66  % (4335)Time elapsed: 0.111 s
% 0.76/0.66  % (4335)------------------------------
% 0.76/0.66  % (4335)------------------------------
% 0.76/0.66  % (4340)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.76/0.66  % (4197)Success in time 0.301 s
%------------------------------------------------------------------------------
