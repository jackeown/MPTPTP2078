%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 122 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 323 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f491,plain,(
    $false ),
    inference(resolution,[],[f478,f209])).

fof(f209,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f21,f200])).

fof(f200,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f21,f120,f70,f54])).

fof(f54,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f70,plain,(
    r2_hidden(sK6(k1_setfam_1(sK1),sK2),k1_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f23,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f23,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f120,plain,(
    ~ r2_hidden(sK6(k1_setfam_1(sK1),sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f22,f71,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,(
    ~ r2_hidden(sK6(k1_setfam_1(sK1),sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f478,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f329,f63])).

fof(f63,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f22,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f329,plain,(
    ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f320,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f320,plain,(
    ~ r2_hidden(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f22,f300,f32])).

fof(f300,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f209,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f56,f63])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.46  % (24707)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.46  % (24699)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (24690)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (24691)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (24705)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (24693)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (24687)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (24713)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (24697)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (24688)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (24690)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f491,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(resolution,[],[f478,f209])).
% 0.22/0.54  fof(f209,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_xboole_0)),
% 0.22/0.54    inference(backward_demodulation,[],[f21,f200])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    k1_xboole_0 = sK1),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f21,f120,f70,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X2,X0,X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0 | ~r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.22/0.54    inference(equality_resolution,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    r2_hidden(sK6(k1_setfam_1(sK1),sK2),k1_setfam_1(sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f23,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ~r1_tarski(k1_setfam_1(sK1),sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & r1_tarski(X0,X2) & r2_hidden(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & (r1_tarski(X0,X2) & r2_hidden(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    ~r2_hidden(sK6(k1_setfam_1(sK1),sK2),sK0)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f22,f71,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ~r2_hidden(sK6(k1_setfam_1(sK1),sK2),sK2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f23,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    r1_tarski(sK0,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    r2_hidden(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f478,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k1_xboole_0)),
% 0.22/0.54    inference(superposition,[],[f329,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f22,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.22/0.54  fof(f329,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(sK0,X0))) )),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f320,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.54  fof(f320,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK0)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f22,f300,f32])).
% 0.22/0.54  fof(f300,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f209,f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK2)) )),
% 0.22/0.54    inference(superposition,[],[f56,f63])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (24690)------------------------------
% 0.22/0.54  % (24690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24690)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (24690)Memory used [KB]: 6396
% 0.22/0.54  % (24690)Time elapsed: 0.132 s
% 0.22/0.54  % (24690)------------------------------
% 0.22/0.54  % (24690)------------------------------
% 0.22/0.54  % (24685)Success in time 0.176 s
%------------------------------------------------------------------------------
