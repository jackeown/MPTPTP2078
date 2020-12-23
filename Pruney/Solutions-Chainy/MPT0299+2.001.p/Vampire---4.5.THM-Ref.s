%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   17 (  34 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  95 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f17])).

fof(f17,plain,(
    r2_hidden(sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f9,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f9,plain,(
    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    & r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
        & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      & r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
      & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
       => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
     => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_zfmisc_1)).

fof(f22,plain,(
    ~ r2_hidden(sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f15,f10,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,plain,(
    ~ r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,plain,(
    r2_hidden(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f9,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (13958)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.48  % (13959)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.48  % (13959)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f22,f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    r2_hidden(sK1,sK3)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f9,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.48    inference(flattening,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ~r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2)) & r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).
% 0.20/0.48  fof(f5,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) => (~r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2)) & r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f4,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)))),
% 0.20/0.48    inference(negated_conjecture,[],[f2])).
% 0.20/0.48  fof(f2,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_zfmisc_1)).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ~r2_hidden(sK1,sK3)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f15,f10,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X0,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ~r2_hidden(k4_tarski(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    r2_hidden(sK0,sK2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f9,f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (13959)------------------------------
% 0.20/0.48  % (13959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (13959)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (13959)Memory used [KB]: 5373
% 0.20/0.48  % (13959)Time elapsed: 0.004 s
% 0.20/0.48  % (13959)------------------------------
% 0.20/0.48  % (13959)------------------------------
% 0.20/0.48  % (13955)WARNING: option uwaf not known.
% 0.20/0.48  % (13951)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.48  % (13955)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.48  % (13944)Success in time 0.123 s
%------------------------------------------------------------------------------
