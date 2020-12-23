%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:37 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 172 expanded)
%              Number of leaves         :    5 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 367 expanded)
%              Number of equality atoms :   44 ( 215 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f107,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X0,X2),k2_tarski(X1,X3))) ),
    inference(unit_resulting_resolution,[],[f44,f44,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f36,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_tarski(X0,X1))
      | ~ sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f36,plain,(
    ! [X3,X1] : sP5(X3,X1,X3) ),
    inference(equality_resolution,[],[f11])).

fof(f11,plain,(
    ! [X0,X3,X1] :
      ( X0 != X3
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f107,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) ),
    inference(backward_demodulation,[],[f105,f106])).

fof(f106,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f103,f105])).

fof(f103,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK3,sK3)))
    | sK1 = sK3 ),
    inference(backward_demodulation,[],[f26,f100])).

fof(f100,plain,(
    sK0 = sK2 ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( sK0 = sK2
    | sK0 = sK2 ),
    inference(resolution,[],[f49,f27])).

fof(f27,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)))
    | sK0 = sK2 ),
    inference(definition_unfolding,[],[f9,f22,f22])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f9,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <~> ( X1 = X3
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      <=> ( X1 = X3
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3))
      | X0 = X2 ) ),
    inference(resolution,[],[f23,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f26,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)))
    | sK1 = sK3 ),
    inference(definition_unfolding,[],[f10,f22,f22])).

fof(f10,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f7])).

fof(f105,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK3,sK3))) ),
    inference(subsumption_resolution,[],[f104,f76])).

fof(f76,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( X8 = X9
      | X8 = X10
      | ~ r2_hidden(k4_tarski(X11,X8),k2_zfmisc_1(X12,k2_tarski(X9,X10))) ) ),
    inference(resolution,[],[f48,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X5,k2_tarski(X6,X4))
      | X5 = X6
      | X4 = X5 ) ),
    inference(resolution,[],[f13,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f104,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK3,sK3)))
    | sK1 != sK3 ),
    inference(subsumption_resolution,[],[f101,f100])).

fof(f101,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK3,sK3)))
    | sK1 != sK3
    | sK0 != sK2 ),
    inference(backward_demodulation,[],[f28,f100])).

fof(f28,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f8,f22,f22])).

fof(f8,plain,
    ( sK0 != sK2
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.31  % Computer   : n021.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % WCLimit    : 600
% 0.13/0.31  % DateTime   : Tue Dec  1 09:26:34 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.17/0.42  % (31167)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.17/0.46  % (31190)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.17/0.46  % (31190)Refutation not found, incomplete strategy% (31190)------------------------------
% 0.17/0.46  % (31190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.46  % (31190)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.46  
% 0.17/0.46  % (31190)Memory used [KB]: 6268
% 0.17/0.46  % (31190)Time elapsed: 0.096 s
% 0.17/0.46  % (31190)------------------------------
% 0.17/0.46  % (31190)------------------------------
% 0.17/0.47  % (31182)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.17/0.47  % (31175)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.17/0.47  % (31178)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.17/0.47  % (31182)Refutation found. Thanks to Tanya!
% 0.17/0.47  % SZS status Theorem for theBenchmark
% 0.17/0.47  % SZS output start Proof for theBenchmark
% 0.17/0.47  fof(f108,plain,(
% 0.17/0.47    $false),
% 0.17/0.47    inference(subsumption_resolution,[],[f107,f65])).
% 0.17/0.47  fof(f65,plain,(
% 0.17/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X0,X2),k2_tarski(X1,X3)))) )),
% 0.17/0.47    inference(unit_resulting_resolution,[],[f44,f44,f25])).
% 0.17/0.47  fof(f25,plain,(
% 0.17/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f4])).
% 0.17/0.47  fof(f4,axiom,(
% 0.17/0.47    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.17/0.47  fof(f44,plain,(
% 0.17/0.47    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.17/0.47    inference(unit_resulting_resolution,[],[f36,f34])).
% 0.17/0.47  fof(f34,plain,(
% 0.17/0.47    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_tarski(X0,X1)) | ~sP5(X3,X1,X0)) )),
% 0.17/0.47    inference(equality_resolution,[],[f14])).
% 0.17/0.47  fof(f14,plain,(
% 0.17/0.47    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.17/0.47    inference(cnf_transformation,[],[f2])).
% 0.17/0.47  fof(f2,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.17/0.47  fof(f36,plain,(
% 0.17/0.47    ( ! [X3,X1] : (sP5(X3,X1,X3)) )),
% 0.17/0.47    inference(equality_resolution,[],[f11])).
% 0.17/0.47  fof(f11,plain,(
% 0.17/0.47    ( ! [X0,X3,X1] : (X0 != X3 | sP5(X3,X1,X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f2])).
% 0.17/0.47  fof(f107,plain,(
% 0.17/0.47    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)))),
% 0.17/0.47    inference(backward_demodulation,[],[f105,f106])).
% 0.17/0.47  fof(f106,plain,(
% 0.17/0.47    sK1 = sK3),
% 0.17/0.47    inference(subsumption_resolution,[],[f103,f105])).
% 0.17/0.47  fof(f103,plain,(
% 0.17/0.47    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK3,sK3))) | sK1 = sK3),
% 0.17/0.47    inference(backward_demodulation,[],[f26,f100])).
% 0.17/0.47  fof(f100,plain,(
% 0.17/0.47    sK0 = sK2),
% 0.17/0.47    inference(duplicate_literal_removal,[],[f94])).
% 0.17/0.47  fof(f94,plain,(
% 0.17/0.47    sK0 = sK2 | sK0 = sK2),
% 0.17/0.47    inference(resolution,[],[f49,f27])).
% 0.17/0.47  fof(f27,plain,(
% 0.17/0.47    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) | sK0 = sK2),
% 0.17/0.47    inference(definition_unfolding,[],[f9,f22,f22])).
% 0.17/0.47  fof(f22,plain,(
% 0.17/0.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f3])).
% 0.17/0.47  fof(f3,axiom,(
% 0.17/0.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.17/0.47  fof(f9,plain,(
% 0.17/0.47    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.17/0.47    inference(cnf_transformation,[],[f7])).
% 0.17/0.47  fof(f7,plain,(
% 0.17/0.47    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <~> (X1 = X3 & X0 = X2))),
% 0.17/0.47    inference(ennf_transformation,[],[f6])).
% 0.17/0.47  fof(f6,negated_conjecture,(
% 0.17/0.47    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.17/0.47    inference(negated_conjecture,[],[f5])).
% 0.17/0.47  fof(f5,conjecture,(
% 0.17/0.47    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 0.17/0.47  fof(f49,plain,(
% 0.17/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3)) | X0 = X2) )),
% 0.17/0.47    inference(resolution,[],[f23,f37])).
% 0.17/0.47  fof(f37,plain,(
% 0.17/0.47    ( ! [X2,X0] : (~r2_hidden(X2,k2_tarski(X0,X0)) | X0 = X2) )),
% 0.17/0.47    inference(equality_resolution,[],[f31])).
% 0.17/0.47  fof(f31,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 0.17/0.47    inference(definition_unfolding,[],[f19,f22])).
% 0.17/0.47  fof(f19,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.17/0.47    inference(cnf_transformation,[],[f1])).
% 0.17/0.47  fof(f1,axiom,(
% 0.17/0.47    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.17/0.47  fof(f23,plain,(
% 0.17/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.17/0.47    inference(cnf_transformation,[],[f4])).
% 0.17/0.47  fof(f26,plain,(
% 0.17/0.47    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) | sK1 = sK3),
% 0.17/0.47    inference(definition_unfolding,[],[f10,f22,f22])).
% 0.17/0.47  fof(f10,plain,(
% 0.17/0.47    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.17/0.47    inference(cnf_transformation,[],[f7])).
% 0.17/0.47  fof(f105,plain,(
% 0.17/0.47    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK3,sK3)))),
% 0.17/0.47    inference(subsumption_resolution,[],[f104,f76])).
% 0.17/0.47  fof(f76,plain,(
% 0.17/0.47    ( ! [X12,X10,X8,X11,X9] : (X8 = X9 | X8 = X10 | ~r2_hidden(k4_tarski(X11,X8),k2_zfmisc_1(X12,k2_tarski(X9,X10)))) )),
% 0.17/0.47    inference(resolution,[],[f48,f24])).
% 0.17/0.48  fof(f24,plain,(
% 0.17/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.17/0.48    inference(cnf_transformation,[],[f4])).
% 0.17/0.48  fof(f48,plain,(
% 0.17/0.48    ( ! [X6,X4,X5] : (~r2_hidden(X5,k2_tarski(X6,X4)) | X5 = X6 | X4 = X5) )),
% 0.17/0.48    inference(resolution,[],[f13,f33])).
% 0.17/0.48  fof(f33,plain,(
% 0.17/0.48    ( ! [X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,k2_tarski(X0,X1))) )),
% 0.17/0.48    inference(equality_resolution,[],[f15])).
% 0.17/0.48  fof(f15,plain,(
% 0.17/0.48    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.17/0.48    inference(cnf_transformation,[],[f2])).
% 0.17/0.48  fof(f13,plain,(
% 0.17/0.48    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 0.17/0.48    inference(cnf_transformation,[],[f2])).
% 0.17/0.48  fof(f104,plain,(
% 0.17/0.48    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK3,sK3))) | sK1 != sK3),
% 0.17/0.48    inference(subsumption_resolution,[],[f101,f100])).
% 0.17/0.48  fof(f101,plain,(
% 0.17/0.48    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK3,sK3))) | sK1 != sK3 | sK0 != sK2),
% 0.17/0.48    inference(backward_demodulation,[],[f28,f100])).
% 0.17/0.48  fof(f28,plain,(
% 0.17/0.48    sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)))),
% 0.17/0.48    inference(definition_unfolding,[],[f8,f22,f22])).
% 0.17/0.48  fof(f8,plain,(
% 0.17/0.48    sK0 != sK2 | sK1 != sK3 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.17/0.48    inference(cnf_transformation,[],[f7])).
% 0.17/0.48  % SZS output end Proof for theBenchmark
% 0.17/0.48  % (31182)------------------------------
% 0.17/0.48  % (31182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.48  % (31182)Termination reason: Refutation
% 0.17/0.48  
% 0.17/0.48  % (31182)Memory used [KB]: 1791
% 0.17/0.48  % (31182)Time elapsed: 0.106 s
% 0.17/0.48  % (31182)------------------------------
% 0.17/0.48  % (31182)------------------------------
% 0.17/0.48  % (31162)Success in time 0.146 s
%------------------------------------------------------------------------------
