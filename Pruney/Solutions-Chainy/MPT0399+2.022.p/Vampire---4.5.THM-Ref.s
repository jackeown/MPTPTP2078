%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  62 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 121 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1407,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f48,f27,f84,f305,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | r2_hidden(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f305,plain,(
    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f22,f56,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(sK2(X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK2(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f20])).

fof(f20,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK2(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f56,plain,(
    r2_hidden(sK1(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f31,f33])).

fof(f33,plain,(
    ! [X0] :
      ( sQ3_eqProxy(k1_xboole_0,X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f26,f30])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f31,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f23,f30])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_setfam_1(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f22,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    ! [X0] : sQ3_eqProxy(sK2(k1_xboole_0),sK2(k2_zfmisc_1(X0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(sK2(X0),sK2(X1))
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f30])).

fof(f27,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f48,plain,(
    ! [X0] : sQ3_eqProxy(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X0] :
      ( sQ3_eqProxy(k1_xboole_0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f25,f30])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f46,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f24,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (3909)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (3897)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.46  % (3897)Refutation not found, incomplete strategy% (3897)------------------------------
% 0.21/0.46  % (3897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (3897)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (3897)Memory used [KB]: 10490
% 0.21/0.46  % (3897)Time elapsed: 0.041 s
% 0.21/0.46  % (3897)------------------------------
% 0.21/0.46  % (3897)------------------------------
% 0.21/0.46  % (3910)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (3910)Refutation not found, incomplete strategy% (3910)------------------------------
% 0.21/0.47  % (3910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3910)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (3910)Memory used [KB]: 6012
% 0.21/0.47  % (3910)Time elapsed: 0.002 s
% 0.21/0.47  % (3910)------------------------------
% 0.21/0.47  % (3910)------------------------------
% 0.21/0.47  % (3898)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (3901)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (3912)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (3909)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f1407,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f48,f27,f84,f305,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | r2_hidden(X1,X3)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    r2_hidden(sK2(k1_xboole_0),k1_xboole_0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f22,f56,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(sK2(X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X1] : (? [X3] : r2_hidden(X3,X1) => r2_hidden(sK2(X1),X1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f31,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(k1_xboole_0,X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f26,f30])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f23,f30])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    r1_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(sK2(k1_xboole_0),sK2(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f48,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(sK2(X0),sK2(X1)) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f30])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f46,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(k1_xboole_0,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f25,f30])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f24,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (3909)------------------------------
% 0.21/0.48  % (3909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3909)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (3909)Memory used [KB]: 11385
% 0.21/0.48  % (3909)Time elapsed: 0.070 s
% 0.21/0.48  % (3909)------------------------------
% 0.21/0.48  % (3909)------------------------------
% 0.21/0.48  % (3891)Success in time 0.123 s
%------------------------------------------------------------------------------
