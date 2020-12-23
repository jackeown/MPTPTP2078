%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:44 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   28 (  88 expanded)
%              Number of leaves         :    5 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 202 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f71,f72,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,(
    r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f47,f57])).

fof(f57,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f10,f41,f40,f33])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f40,plain,(
    r2_hidden(sK2(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f11,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f41,plain,(
    ~ r2_hidden(sK2(k1_setfam_1(sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f11,f14])).

fof(f10,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,(
    r2_hidden(sK2(sK1,k1_xboole_0),sK1) ),
    inference(unit_resulting_resolution,[],[f46,f13])).

fof(f46,plain,(
    ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(superposition,[],[f36,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f36,plain,(
    ! [X0] : ~ r1_tarski(sK1,k2_zfmisc_1(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f23,f10,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f71,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f46,f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:21:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (5825)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (5841)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (5816)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.54  % (5833)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.55  % (5833)Refutation not found, incomplete strategy% (5833)------------------------------
% 1.37/0.55  % (5833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (5833)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (5833)Memory used [KB]: 1663
% 1.37/0.55  % (5833)Time elapsed: 0.129 s
% 1.37/0.55  % (5833)------------------------------
% 1.37/0.55  % (5833)------------------------------
% 1.37/0.56  % (5815)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.51/0.56  % (5817)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.51/0.57  % (5816)Refutation found. Thanks to Tanya!
% 1.51/0.57  % SZS status Theorem for theBenchmark
% 1.51/0.57  % SZS output start Proof for theBenchmark
% 1.51/0.57  fof(f109,plain,(
% 1.51/0.57    $false),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f71,f72,f14])).
% 1.51/0.57  fof(f14,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f8])).
% 1.51/0.57  fof(f8,plain,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f1])).
% 1.51/0.57  fof(f1,axiom,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.57  fof(f72,plain,(
% 1.51/0.57    r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.51/0.57    inference(backward_demodulation,[],[f47,f57])).
% 1.51/0.57  fof(f57,plain,(
% 1.51/0.57    k1_xboole_0 = sK1),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f10,f41,f40,f33])).
% 1.51/0.57  fof(f33,plain,(
% 1.51/0.57    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | k1_xboole_0 = X0 | r2_hidden(X2,X3) | ~r2_hidden(X2,k1_setfam_1(X0))) )),
% 1.51/0.57    inference(equality_resolution,[],[f18])).
% 1.51/0.57  fof(f18,plain,(
% 1.51/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 1.51/0.57    inference(cnf_transformation,[],[f9])).
% 1.51/0.57  fof(f9,plain,(
% 1.51/0.57    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 1.51/0.57    inference(ennf_transformation,[],[f4])).
% 1.51/0.57  fof(f4,axiom,(
% 1.51/0.57    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 1.51/0.57  fof(f40,plain,(
% 1.51/0.57    r2_hidden(sK2(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1))),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f11,f13])).
% 1.51/0.57  fof(f13,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f8])).
% 1.51/0.57  fof(f11,plain,(
% 1.51/0.57    ~r1_tarski(k1_setfam_1(sK1),sK0)),
% 1.51/0.57    inference(cnf_transformation,[],[f7])).
% 1.51/0.57  fof(f7,plain,(
% 1.51/0.57    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),X0) & r2_hidden(X0,X1))),
% 1.51/0.57    inference(ennf_transformation,[],[f6])).
% 1.51/0.57  fof(f6,negated_conjecture,(
% 1.51/0.57    ~! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.51/0.57    inference(negated_conjecture,[],[f5])).
% 1.51/0.57  fof(f5,conjecture,(
% 1.51/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.51/0.57  fof(f41,plain,(
% 1.51/0.57    ~r2_hidden(sK2(k1_setfam_1(sK1),sK0),sK0)),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f11,f14])).
% 1.51/0.57  fof(f10,plain,(
% 1.51/0.57    r2_hidden(sK0,sK1)),
% 1.51/0.57    inference(cnf_transformation,[],[f7])).
% 1.51/0.57  fof(f47,plain,(
% 1.51/0.57    r2_hidden(sK2(sK1,k1_xboole_0),sK1)),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f46,f13])).
% 1.51/0.57  fof(f46,plain,(
% 1.51/0.57    ~r1_tarski(sK1,k1_xboole_0)),
% 1.51/0.57    inference(superposition,[],[f36,f34])).
% 1.51/0.57  fof(f34,plain,(
% 1.51/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.51/0.57    inference(equality_resolution,[],[f26])).
% 1.51/0.57  fof(f26,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.51/0.57    inference(cnf_transformation,[],[f2])).
% 1.51/0.57  fof(f2,axiom,(
% 1.51/0.57    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.51/0.57  fof(f36,plain,(
% 1.51/0.57    ( ! [X0] : (~r1_tarski(sK1,k2_zfmisc_1(sK0,X0))) )),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f23,f10,f12])).
% 1.51/0.57  fof(f12,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f8])).
% 1.51/0.57  fof(f23,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f3])).
% 1.51/0.57  fof(f3,axiom,(
% 1.51/0.57    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.51/0.57  fof(f71,plain,(
% 1.51/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.51/0.57    inference(backward_demodulation,[],[f46,f57])).
% 1.51/0.57  % SZS output end Proof for theBenchmark
% 1.51/0.57  % (5816)------------------------------
% 1.51/0.57  % (5816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (5816)Termination reason: Refutation
% 1.51/0.57  
% 1.51/0.57  % (5816)Memory used [KB]: 6268
% 1.51/0.57  % (5816)Time elapsed: 0.150 s
% 1.51/0.57  % (5816)------------------------------
% 1.51/0.57  % (5816)------------------------------
% 1.51/0.57  % (5811)Success in time 0.203 s
%------------------------------------------------------------------------------
