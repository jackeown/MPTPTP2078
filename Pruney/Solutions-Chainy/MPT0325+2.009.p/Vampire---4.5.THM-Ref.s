%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:39 EST 2020

% Result     : Theorem 15.86s
% Output     : Refutation 15.86s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 215 expanded)
%              Number of leaves         :   12 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  129 ( 411 expanded)
%              Number of equality atoms :   43 ( 147 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12448,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10982,f203])).

fof(f203,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f141,f144,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | sP7(sK6(X0,X1,X2),X1,X0)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f144,plain,(
    ! [X0,X1] : ~ sP7(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f141,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X0)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f141,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f138,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f138,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(unit_resulting_resolution,[],[f84,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f46,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f84,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f72,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f10982,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f27,f10979])).

fof(f10979,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f10882,f204])).

fof(f204,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f141,f145,f54])).

fof(f145,plain,(
    ! [X0,X1] : ~ sP7(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f141,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X1)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f10882,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f27,f10725])).

fof(f10725,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f10639,f9398])).

fof(f9398,plain,
    ( r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f9385,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f9385,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f9345,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f9345,plain,(
    r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k2_zfmisc_1(sK2,sK1)) ),
    inference(superposition,[],[f842,f69])).

fof(f69,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f842,plain,(
    ! [X61,X64,X62,X63] : r1_tarski(k4_xboole_0(k2_zfmisc_1(X63,X62),k4_xboole_0(k2_zfmisc_1(X63,X62),k2_zfmisc_1(X61,X64))),k2_zfmisc_1(X61,X62)) ),
    inference(forward_demodulation,[],[f772,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f28,f36,f36,f36])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f772,plain,(
    ! [X61,X64,X62,X63] : r1_tarski(k2_zfmisc_1(k4_xboole_0(X63,k4_xboole_0(X63,X61)),k4_xboole_0(X62,k4_xboole_0(X62,X64))),k2_zfmisc_1(X61,X62)) ),
    inference(superposition,[],[f79,f225])).

fof(f225,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f56,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f36,f36])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f10639,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f10214,f25])).

fof(f25,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f10214,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f9853,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9853,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(forward_demodulation,[],[f9811,f38])).

fof(f9811,plain,(
    r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k2_zfmisc_1(sK0,sK3)) ),
    inference(superposition,[],[f985,f69])).

fof(f985,plain,(
    ! [X80,X78,X79,X77] : r1_tarski(k4_xboole_0(k2_zfmisc_1(X77,X80),k4_xboole_0(k2_zfmisc_1(X77,X80),k2_zfmisc_1(X79,X78))),k2_zfmisc_1(X77,X78)) ),
    inference(forward_demodulation,[],[f906,f56])).

fof(f906,plain,(
    ! [X80,X78,X79,X77] : r1_tarski(k2_zfmisc_1(k4_xboole_0(X77,k4_xboole_0(X77,X79)),k4_xboole_0(X80,k4_xboole_0(X80,X78))),k2_zfmisc_1(X77,X78)) ),
    inference(superposition,[],[f79,f234])).

fof(f234,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))) = k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f56,f57])).

fof(f27,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (8646)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.48  % (8673)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.49  % (8655)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (8668)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (8665)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (8669)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (8649)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (8660)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (8653)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (8652)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (8647)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (8651)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (8650)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (8671)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (8675)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (8672)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (8663)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.55  % (8667)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.55  % (8664)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.44/0.55  % (8654)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.44/0.55  % (8658)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.44/0.55  % (8657)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.55  % (8659)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.44/0.55  % (8674)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.44/0.56  % (8674)Refutation not found, incomplete strategy% (8674)------------------------------
% 1.44/0.56  % (8674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (8674)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (8674)Memory used [KB]: 10746
% 1.44/0.56  % (8674)Time elapsed: 0.148 s
% 1.44/0.56  % (8674)------------------------------
% 1.44/0.56  % (8674)------------------------------
% 1.44/0.56  % (8648)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.44/0.56  % (8661)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.59/0.57  % (8666)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.59/0.57  % (8656)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.59/0.57  % (8670)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.59/0.58  % (8662)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.59/0.58  % (8662)Refutation not found, incomplete strategy% (8662)------------------------------
% 1.59/0.58  % (8662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (8662)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (8662)Memory used [KB]: 10618
% 1.59/0.59  % (8662)Time elapsed: 0.181 s
% 1.59/0.59  % (8662)------------------------------
% 1.59/0.59  % (8662)------------------------------
% 2.32/0.72  % (8693)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.85/0.76  % (8698)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.07/0.83  % (8648)Time limit reached!
% 3.07/0.83  % (8648)------------------------------
% 3.07/0.83  % (8648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.83  % (8648)Termination reason: Time limit
% 3.07/0.83  
% 3.07/0.83  % (8648)Memory used [KB]: 6524
% 3.07/0.83  % (8648)Time elapsed: 0.427 s
% 3.07/0.83  % (8648)------------------------------
% 3.07/0.83  % (8648)------------------------------
% 3.07/0.83  % (8670)Time limit reached!
% 3.07/0.83  % (8670)------------------------------
% 3.07/0.83  % (8670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.83  % (8670)Termination reason: Time limit
% 3.07/0.83  
% 3.07/0.83  % (8670)Memory used [KB]: 12665
% 3.07/0.83  % (8670)Time elapsed: 0.428 s
% 3.07/0.83  % (8670)------------------------------
% 3.07/0.83  % (8670)------------------------------
% 3.85/0.92  % (8675)Time limit reached!
% 3.85/0.92  % (8675)------------------------------
% 3.85/0.92  % (8675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.92  % (8675)Termination reason: Time limit
% 3.85/0.92  % (8675)Termination phase: Saturation
% 3.85/0.92  
% 3.85/0.92  % (8675)Memory used [KB]: 5756
% 3.85/0.92  % (8675)Time elapsed: 0.518 s
% 3.85/0.92  % (8675)------------------------------
% 3.85/0.92  % (8675)------------------------------
% 4.27/0.96  % (8652)Time limit reached!
% 4.27/0.96  % (8652)------------------------------
% 4.27/0.96  % (8652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.96  % (8652)Termination reason: Time limit
% 4.27/0.96  
% 4.27/0.96  % (8652)Memory used [KB]: 16886
% 4.27/0.96  % (8652)Time elapsed: 0.512 s
% 4.27/0.96  % (8652)------------------------------
% 4.27/0.96  % (8652)------------------------------
% 4.52/0.97  % (8706)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.52/0.99  % (8707)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.52/1.01  % (8660)Time limit reached!
% 4.52/1.01  % (8660)------------------------------
% 4.52/1.01  % (8660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/1.01  % (8660)Termination reason: Time limit
% 4.52/1.01  
% 4.52/1.01  % (8660)Memory used [KB]: 7419
% 4.52/1.01  % (8660)Time elapsed: 0.534 s
% 4.52/1.01  % (8660)------------------------------
% 4.52/1.01  % (8660)------------------------------
% 4.52/1.01  % (8653)Time limit reached!
% 4.52/1.01  % (8653)------------------------------
% 4.52/1.01  % (8653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/1.01  % (8653)Termination reason: Time limit
% 4.52/1.01  
% 4.52/1.01  % (8653)Memory used [KB]: 5373
% 4.52/1.01  % (8653)Time elapsed: 0.620 s
% 4.52/1.01  % (8653)------------------------------
% 4.52/1.01  % (8653)------------------------------
% 4.99/1.06  % (8708)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.65/1.09  % (8709)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.16/1.14  % (8710)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.16/1.15  % (8711)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.38/1.21  % (8647)Time limit reached!
% 6.38/1.21  % (8647)------------------------------
% 6.38/1.21  % (8647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.38/1.21  % (8647)Termination reason: Time limit
% 6.38/1.21  
% 6.38/1.21  % (8647)Memory used [KB]: 7291
% 6.38/1.21  % (8647)Time elapsed: 0.804 s
% 6.38/1.21  % (8647)------------------------------
% 6.38/1.21  % (8647)------------------------------
% 7.60/1.32  % (8649)Time limit reached!
% 7.60/1.32  % (8649)------------------------------
% 7.60/1.32  % (8649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.60/1.32  % (8649)Termination reason: Time limit
% 7.60/1.32  
% 7.60/1.32  % (8649)Memory used [KB]: 9850
% 7.60/1.32  % (8649)Time elapsed: 0.920 s
% 7.60/1.32  % (8649)------------------------------
% 7.60/1.32  % (8649)------------------------------
% 7.60/1.36  % (8712)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 7.91/1.41  % (8673)Time limit reached!
% 7.91/1.41  % (8673)------------------------------
% 7.91/1.41  % (8673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.41  % (8673)Termination reason: Time limit
% 7.91/1.41  % (8673)Termination phase: Saturation
% 7.91/1.41  
% 7.91/1.41  % (8673)Memory used [KB]: 14328
% 7.91/1.41  % (8673)Time elapsed: 1.0000 s
% 7.91/1.41  % (8673)------------------------------
% 7.91/1.41  % (8673)------------------------------
% 7.91/1.42  % (8658)Time limit reached!
% 7.91/1.42  % (8658)------------------------------
% 7.91/1.42  % (8658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.42  % (8658)Termination reason: Time limit
% 7.91/1.42  
% 7.91/1.42  % (8658)Memory used [KB]: 14328
% 7.91/1.42  % (8658)Time elapsed: 1.009 s
% 7.91/1.42  % (8658)------------------------------
% 7.91/1.42  % (8658)------------------------------
% 8.47/1.47  % (8713)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.05/1.53  % (8715)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.24/1.55  % (8714)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.24/1.59  % (8646)Time limit reached!
% 9.24/1.59  % (8646)------------------------------
% 9.24/1.59  % (8646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.24/1.60  % (8646)Termination reason: Time limit
% 9.24/1.60  % (8646)Termination phase: Saturation
% 9.24/1.60  
% 9.24/1.60  % (8646)Memory used [KB]: 8827
% 9.24/1.60  % (8646)Time elapsed: 1.200 s
% 9.24/1.60  % (8646)------------------------------
% 9.24/1.60  % (8646)------------------------------
% 10.00/1.66  % (8706)Time limit reached!
% 10.00/1.66  % (8706)------------------------------
% 10.00/1.66  % (8706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.00/1.66  % (8706)Termination reason: Time limit
% 10.00/1.66  % (8706)Termination phase: Saturation
% 10.00/1.66  
% 10.00/1.66  % (8706)Memory used [KB]: 13688
% 10.00/1.66  % (8706)Time elapsed: 0.800 s
% 10.00/1.66  % (8706)------------------------------
% 10.00/1.66  % (8706)------------------------------
% 10.00/1.67  % (8710)Time limit reached!
% 10.00/1.67  % (8710)------------------------------
% 10.00/1.67  % (8710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.00/1.67  % (8710)Termination reason: Time limit
% 10.00/1.67  % (8710)Termination phase: Saturation
% 10.00/1.67  
% 10.00/1.67  % (8710)Memory used [KB]: 17654
% 10.00/1.67  % (8710)Time elapsed: 0.600 s
% 10.00/1.67  % (8710)------------------------------
% 10.00/1.67  % (8710)------------------------------
% 10.41/1.72  % (8651)Time limit reached!
% 10.41/1.72  % (8651)------------------------------
% 10.41/1.72  % (8651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.41/1.72  % (8651)Termination reason: Time limit
% 10.41/1.72  % (8651)Termination phase: Saturation
% 10.41/1.72  
% 10.41/1.72  % (8651)Memory used [KB]: 9722
% 10.41/1.72  % (8651)Time elapsed: 1.300 s
% 10.41/1.72  % (8651)------------------------------
% 10.41/1.72  % (8651)------------------------------
% 10.41/1.75  % (8716)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 11.17/1.80  % (8717)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.17/1.80  % (8718)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.64/1.86  % (8719)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 12.19/1.95  % (8718)Refutation not found, incomplete strategy% (8718)------------------------------
% 12.19/1.95  % (8718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.19/1.95  % (8718)Termination reason: Refutation not found, incomplete strategy
% 12.19/1.95  
% 12.19/1.95  % (8718)Memory used [KB]: 6268
% 12.19/1.95  % (8718)Time elapsed: 0.257 s
% 12.19/1.95  % (8718)------------------------------
% 12.19/1.95  % (8718)------------------------------
% 12.66/2.01  % (8672)Time limit reached!
% 12.66/2.01  % (8672)------------------------------
% 12.66/2.01  % (8672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.66/2.01  % (8672)Termination reason: Time limit
% 12.66/2.01  % (8672)Termination phase: Saturation
% 12.66/2.01  
% 12.66/2.01  % (8672)Memory used [KB]: 20980
% 12.66/2.01  % (8672)Time elapsed: 1.600 s
% 12.66/2.01  % (8672)------------------------------
% 12.66/2.01  % (8672)------------------------------
% 13.36/2.09  % (8720)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 13.36/2.10  % (8717)Time limit reached!
% 13.36/2.10  % (8717)------------------------------
% 13.36/2.10  % (8717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.36/2.10  % (8717)Termination reason: Time limit
% 13.36/2.10  % (8717)Termination phase: Saturation
% 13.36/2.10  
% 13.36/2.10  % (8717)Memory used [KB]: 13944
% 13.36/2.10  % (8717)Time elapsed: 0.400 s
% 13.36/2.10  % (8717)------------------------------
% 13.36/2.10  % (8717)------------------------------
% 13.80/2.14  % (8719)Time limit reached!
% 13.80/2.14  % (8719)------------------------------
% 13.80/2.14  % (8719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.80/2.14  % (8719)Termination reason: Time limit
% 13.80/2.14  % (8719)Termination phase: Saturation
% 13.80/2.14  
% 13.80/2.14  % (8719)Memory used [KB]: 7547
% 13.80/2.14  % (8719)Time elapsed: 0.400 s
% 13.80/2.14  % (8719)------------------------------
% 13.80/2.14  % (8719)------------------------------
% 13.80/2.14  % (8721)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 14.20/2.17  % (8713)Time limit reached!
% 14.20/2.17  % (8713)------------------------------
% 14.20/2.17  % (8713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.20/2.17  % (8713)Termination reason: Time limit
% 14.20/2.17  
% 14.20/2.17  % (8713)Memory used [KB]: 16247
% 14.20/2.17  % (8713)Time elapsed: 0.815 s
% 14.20/2.17  % (8713)------------------------------
% 14.20/2.17  % (8713)------------------------------
% 14.82/2.24  % (8722)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 15.22/2.30  % (8723)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 15.22/2.31  % (8724)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 15.22/2.35  % (8666)Time limit reached!
% 15.22/2.35  % (8666)------------------------------
% 15.22/2.35  % (8666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.22/2.35  % (8666)Termination reason: Time limit
% 15.22/2.35  
% 15.22/2.35  % (8666)Memory used [KB]: 23155
% 15.22/2.35  % (8666)Time elapsed: 1.932 s
% 15.22/2.35  % (8666)------------------------------
% 15.22/2.35  % (8666)------------------------------
% 15.86/2.37  % (8665)Refutation found. Thanks to Tanya!
% 15.86/2.37  % SZS status Theorem for theBenchmark
% 15.86/2.37  % SZS output start Proof for theBenchmark
% 15.86/2.37  fof(f12448,plain,(
% 15.86/2.37    $false),
% 15.86/2.37    inference(subsumption_resolution,[],[f10982,f203])).
% 15.86/2.37  fof(f203,plain,(
% 15.86/2.37    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 15.86/2.37    inference(unit_resulting_resolution,[],[f141,f144,f54])).
% 15.86/2.37  fof(f54,plain,(
% 15.86/2.37    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | sP7(sK6(X0,X1,X2),X1,X0) | k2_zfmisc_1(X0,X1) = X2) )),
% 15.86/2.37    inference(cnf_transformation,[],[f11])).
% 15.86/2.37  fof(f11,axiom,(
% 15.86/2.37    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 15.86/2.37  fof(f144,plain,(
% 15.86/2.37    ( ! [X0,X1] : (~sP7(X0,X1,k1_xboole_0)) )),
% 15.86/2.37    inference(unit_resulting_resolution,[],[f141,f49])).
% 15.86/2.37  fof(f49,plain,(
% 15.86/2.37    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X0) | ~sP7(X3,X1,X0)) )),
% 15.86/2.37    inference(cnf_transformation,[],[f11])).
% 15.86/2.37  fof(f141,plain,(
% 15.86/2.37    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 15.86/2.37    inference(forward_demodulation,[],[f138,f40])).
% 15.86/2.37  fof(f40,plain,(
% 15.86/2.37    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 15.86/2.37    inference(cnf_transformation,[],[f10])).
% 15.86/2.37  fof(f10,axiom,(
% 15.86/2.37    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 15.86/2.37  fof(f138,plain,(
% 15.86/2.37    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))) )),
% 15.86/2.37    inference(unit_resulting_resolution,[],[f84,f60])).
% 15.86/2.37  fof(f60,plain,(
% 15.86/2.37    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.86/2.37    inference(definition_unfolding,[],[f46,f36])).
% 15.86/2.37  fof(f36,plain,(
% 15.86/2.37    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.86/2.37    inference(cnf_transformation,[],[f9])).
% 15.86/2.37  fof(f9,axiom,(
% 15.86/2.37    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 15.86/2.37  fof(f46,plain,(
% 15.86/2.37    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 15.86/2.37    inference(cnf_transformation,[],[f24])).
% 15.86/2.37  fof(f24,plain,(
% 15.86/2.37    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.86/2.37    inference(ennf_transformation,[],[f17])).
% 15.86/2.37  fof(f17,plain,(
% 15.86/2.37    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.86/2.37    inference(rectify,[],[f2])).
% 15.86/2.37  fof(f2,axiom,(
% 15.86/2.37    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 15.86/2.37  fof(f84,plain,(
% 15.86/2.37    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 15.86/2.37    inference(unit_resulting_resolution,[],[f72,f43])).
% 15.86/2.37  fof(f43,plain,(
% 15.86/2.37    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 15.86/2.37    inference(cnf_transformation,[],[f22])).
% 15.86/2.37  fof(f22,plain,(
% 15.86/2.37    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 15.86/2.37    inference(ennf_transformation,[],[f6])).
% 15.86/2.37  fof(f6,axiom,(
% 15.86/2.37    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 15.86/2.37  fof(f72,plain,(
% 15.86/2.37    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.86/2.37    inference(unit_resulting_resolution,[],[f40,f32])).
% 15.86/2.37  fof(f32,plain,(
% 15.86/2.37    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 15.86/2.37    inference(cnf_transformation,[],[f5])).
% 15.86/2.37  fof(f5,axiom,(
% 15.86/2.37    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 15.86/2.37  fof(f10982,plain,(
% 15.86/2.37    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 15.86/2.37    inference(backward_demodulation,[],[f27,f10979])).
% 15.86/2.37  fof(f10979,plain,(
% 15.86/2.37    k1_xboole_0 = sK0),
% 15.86/2.37    inference(subsumption_resolution,[],[f10882,f204])).
% 15.86/2.37  fof(f204,plain,(
% 15.86/2.37    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.86/2.37    inference(unit_resulting_resolution,[],[f141,f145,f54])).
% 15.86/2.37  fof(f145,plain,(
% 15.86/2.37    ( ! [X0,X1] : (~sP7(X0,k1_xboole_0,X1)) )),
% 15.86/2.37    inference(unit_resulting_resolution,[],[f141,f50])).
% 15.86/2.37  fof(f50,plain,(
% 15.86/2.37    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X1) | ~sP7(X3,X1,X0)) )),
% 15.86/2.37    inference(cnf_transformation,[],[f11])).
% 15.86/2.37  fof(f10882,plain,(
% 15.86/2.37    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 15.86/2.37    inference(superposition,[],[f27,f10725])).
% 15.86/2.37  fof(f10725,plain,(
% 15.86/2.37    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 15.86/2.37    inference(resolution,[],[f10639,f9398])).
% 15.86/2.37  fof(f9398,plain,(
% 15.86/2.37    r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 15.86/2.37    inference(resolution,[],[f9385,f29])).
% 15.86/2.37  fof(f29,plain,(
% 15.86/2.37    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 15.86/2.37    inference(cnf_transformation,[],[f20])).
% 15.86/2.37  fof(f20,plain,(
% 15.86/2.37    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 15.86/2.37    inference(ennf_transformation,[],[f12])).
% 15.86/2.37  fof(f12,axiom,(
% 15.86/2.37    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 15.86/2.37  fof(f9385,plain,(
% 15.86/2.37    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 15.86/2.37    inference(forward_demodulation,[],[f9345,f38])).
% 15.86/2.37  fof(f38,plain,(
% 15.86/2.37    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.86/2.37    inference(cnf_transformation,[],[f8])).
% 15.86/2.37  fof(f8,axiom,(
% 15.86/2.37    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 15.86/2.37  fof(f9345,plain,(
% 15.86/2.37    r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k2_zfmisc_1(sK2,sK1))),
% 15.86/2.37    inference(superposition,[],[f842,f69])).
% 15.86/2.37  fof(f69,plain,(
% 15.86/2.37    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 15.86/2.37    inference(unit_resulting_resolution,[],[f26,f31])).
% 15.86/2.37  fof(f31,plain,(
% 15.86/2.37    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 15.86/2.37    inference(cnf_transformation,[],[f5])).
% 15.86/2.37  fof(f26,plain,(
% 15.86/2.37    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 15.86/2.37    inference(cnf_transformation,[],[f19])).
% 15.86/2.37  fof(f19,plain,(
% 15.86/2.37    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 15.86/2.37    inference(flattening,[],[f18])).
% 15.86/2.37  fof(f18,plain,(
% 15.86/2.37    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 15.86/2.37    inference(ennf_transformation,[],[f16])).
% 15.86/2.37  fof(f16,negated_conjecture,(
% 15.86/2.37    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 15.86/2.37    inference(negated_conjecture,[],[f15])).
% 15.86/2.37  fof(f15,conjecture,(
% 15.86/2.37    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 15.86/2.37  fof(f842,plain,(
% 15.86/2.37    ( ! [X61,X64,X62,X63] : (r1_tarski(k4_xboole_0(k2_zfmisc_1(X63,X62),k4_xboole_0(k2_zfmisc_1(X63,X62),k2_zfmisc_1(X61,X64))),k2_zfmisc_1(X61,X62))) )),
% 15.86/2.37    inference(forward_demodulation,[],[f772,f56])).
% 15.86/2.37  fof(f56,plain,(
% 15.86/2.37    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 15.86/2.37    inference(definition_unfolding,[],[f28,f36,f36,f36])).
% 15.86/2.37  fof(f28,plain,(
% 15.86/2.37    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 15.86/2.37    inference(cnf_transformation,[],[f14])).
% 15.86/2.37  fof(f14,axiom,(
% 15.86/2.37    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 15.86/2.37  fof(f772,plain,(
% 15.86/2.37    ( ! [X61,X64,X62,X63] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(X63,k4_xboole_0(X63,X61)),k4_xboole_0(X62,k4_xboole_0(X62,X64))),k2_zfmisc_1(X61,X62))) )),
% 15.86/2.37    inference(superposition,[],[f79,f225])).
% 15.86/2.37  fof(f225,plain,(
% 15.86/2.37    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 15.86/2.37    inference(superposition,[],[f56,f57])).
% 15.86/2.37  fof(f57,plain,(
% 15.86/2.37    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 15.86/2.37    inference(definition_unfolding,[],[f37,f36,f36])).
% 15.86/2.37  fof(f37,plain,(
% 15.86/2.37    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.86/2.37    inference(cnf_transformation,[],[f1])).
% 15.86/2.37  fof(f1,axiom,(
% 15.86/2.37    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 15.86/2.37  fof(f79,plain,(
% 15.86/2.37    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.86/2.37    inference(unit_resulting_resolution,[],[f61,f42])).
% 15.86/2.37  fof(f42,plain,(
% 15.86/2.37    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 15.86/2.37    inference(cnf_transformation,[],[f22])).
% 15.86/2.37  fof(f61,plain,(
% 15.86/2.37    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.86/2.37    inference(equality_resolution,[],[f34])).
% 15.86/2.37  fof(f34,plain,(
% 15.86/2.37    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 15.86/2.37    inference(cnf_transformation,[],[f4])).
% 15.86/2.37  fof(f4,axiom,(
% 15.86/2.37    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.86/2.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 15.86/2.37  fof(f10639,plain,(
% 15.86/2.37    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0),
% 15.86/2.37    inference(resolution,[],[f10214,f25])).
% 15.86/2.37  fof(f25,plain,(
% 15.86/2.37    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 15.86/2.37    inference(cnf_transformation,[],[f19])).
% 15.86/2.37  fof(f10214,plain,(
% 15.86/2.37    r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 15.86/2.37    inference(resolution,[],[f9853,f30])).
% 15.86/2.37  fof(f30,plain,(
% 15.86/2.37    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 15.86/2.37    inference(cnf_transformation,[],[f20])).
% 15.86/2.37  fof(f9853,plain,(
% 15.86/2.37    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 15.86/2.37    inference(forward_demodulation,[],[f9811,f38])).
% 15.86/2.37  fof(f9811,plain,(
% 15.86/2.37    r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0),k2_zfmisc_1(sK0,sK3))),
% 15.86/2.37    inference(superposition,[],[f985,f69])).
% 15.86/2.37  fof(f985,plain,(
% 15.86/2.37    ( ! [X80,X78,X79,X77] : (r1_tarski(k4_xboole_0(k2_zfmisc_1(X77,X80),k4_xboole_0(k2_zfmisc_1(X77,X80),k2_zfmisc_1(X79,X78))),k2_zfmisc_1(X77,X78))) )),
% 15.86/2.37    inference(forward_demodulation,[],[f906,f56])).
% 15.86/2.37  fof(f906,plain,(
% 15.86/2.37    ( ! [X80,X78,X79,X77] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(X77,k4_xboole_0(X77,X79)),k4_xboole_0(X80,k4_xboole_0(X80,X78))),k2_zfmisc_1(X77,X78))) )),
% 15.86/2.37    inference(superposition,[],[f79,f234])).
% 15.86/2.37  fof(f234,plain,(
% 15.86/2.37    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))) = k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 15.86/2.37    inference(superposition,[],[f56,f57])).
% 15.86/2.37  fof(f27,plain,(
% 15.86/2.37    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 15.86/2.37    inference(cnf_transformation,[],[f19])).
% 15.86/2.37  % SZS output end Proof for theBenchmark
% 15.86/2.37  % (8665)------------------------------
% 15.86/2.37  % (8665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.86/2.37  % (8665)Termination reason: Refutation
% 15.86/2.37  
% 15.86/2.37  % (8665)Memory used [KB]: 15095
% 15.86/2.37  % (8665)Time elapsed: 1.905 s
% 15.86/2.37  % (8665)------------------------------
% 15.86/2.37  % (8665)------------------------------
% 15.86/2.40  % (8642)Success in time 2.027 s
%------------------------------------------------------------------------------
