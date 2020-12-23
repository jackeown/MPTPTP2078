%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:02 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 268 expanded)
%              Number of leaves         :    9 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  148 ( 842 expanded)
%              Number of equality atoms :   25 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3109,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3085,f22])).

fof(f22,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f3085,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f23,f3067])).

fof(f3067,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f2567,f2897])).

fof(f2897,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X5,X5)) = X4 ),
    inference(superposition,[],[f102,f2449])).

fof(f2449,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f1785,f1785])).

fof(f1785,plain,(
    ! [X16] : k4_xboole_0(X16,X16) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f1771,f661])).

fof(f661,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f658])).

fof(f658,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1
      | r2_hidden(sK5(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1771,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1768,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1768,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k4_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f1761,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1761,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f1751,f1324])).

fof(f1324,plain,(
    ! [X28] :
      ( ~ r1_xboole_0(k4_xboole_0(X28,sK1),sK2)
      | r1_xboole_0(k4_xboole_0(X28,sK1),sK0) ) ),
    inference(resolution,[],[f1307,f255])).

fof(f255,plain,(
    ! [X6] :
      ( ~ r1_xboole_0(X6,sK1)
      | ~ r1_xboole_0(X6,sK2)
      | r1_xboole_0(X6,sK0) ) ),
    inference(resolution,[],[f36,f66])).

fof(f66,plain,(
    ! [X8] :
      ( ~ r1_xboole_0(X8,k2_xboole_0(sK1,sK2))
      | r1_xboole_0(X8,sK0) ) ),
    inference(superposition,[],[f34,f52])).

fof(f52,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f29,f20])).

fof(f20,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1307,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f1302])).

fof(f1302,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X0,X1),X1)
      | r1_xboole_0(k4_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f71,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X1)
      | r1_xboole_0(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f44,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1751,plain,(
    ! [X14] : r1_xboole_0(k4_xboole_0(sK0,X14),sK2) ),
    inference(duplicate_literal_removal,[],[f1727])).

fof(f1727,plain,(
    ! [X14] :
      ( r1_xboole_0(k4_xboole_0(sK0,X14),sK2)
      | r1_xboole_0(k4_xboole_0(sK0,X14),sK2) ) ),
    inference(resolution,[],[f74,f142])).

fof(f142,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(X1,sK2),sK0)
      | r1_xboole_0(X1,sK2) ) ),
    inference(resolution,[],[f126,f28])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f26,f21])).

fof(f21,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X0)
      | r1_xboole_0(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f45,f27])).

fof(f102,plain,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(superposition,[],[f92,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f92,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(resolution,[],[f88,f29])).

fof(f88,plain,(
    ! [X4] : r1_tarski(k4_xboole_0(X4,X4),X4) ),
    inference(superposition,[],[f83,f60])).

fof(f60,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f59,f29])).

fof(f59,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f48,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f23,f24])).

fof(f2567,plain,(
    ! [X15] : k2_xboole_0(sK1,k4_xboole_0(X15,X15)) = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f2528,f24])).

fof(f2528,plain,(
    ! [X15] : k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k4_xboole_0(X15,X15)) ),
    inference(superposition,[],[f25,f1785])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:06:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (9548)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (9550)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (9542)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (9564)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (9556)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.56  % (9543)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.56  % (9538)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.56  % (9545)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % (9536)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.57  % (9540)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.57  % (9558)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.58  % (9544)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.59  % (9559)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.59  % (9537)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.60  % (9539)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.60  % (9553)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.60  % (9560)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.60  % (9551)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.60  % (9563)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.61  % (9554)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.79/0.61  % (9555)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.79/0.62  % (9562)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.79/0.62  % (9552)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.02/0.64  % (9541)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 2.02/0.64  % (9547)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.02/0.64  % (9546)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.23/0.68  % (9565)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.23/0.68  % (9561)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.23/0.68  % (9549)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.23/0.69  % (9557)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.81/0.75  % (9542)Refutation found. Thanks to Tanya!
% 2.81/0.75  % SZS status Theorem for theBenchmark
% 2.81/0.75  % SZS output start Proof for theBenchmark
% 2.81/0.75  fof(f3109,plain,(
% 2.81/0.75    $false),
% 2.81/0.75    inference(subsumption_resolution,[],[f3085,f22])).
% 2.81/0.75  fof(f22,plain,(
% 2.81/0.75    ~r1_tarski(sK0,sK1)),
% 2.81/0.75    inference(cnf_transformation,[],[f14])).
% 2.81/0.75  fof(f14,plain,(
% 2.81/0.75    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.81/0.75    inference(flattening,[],[f13])).
% 2.81/0.75  fof(f13,plain,(
% 2.81/0.75    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.81/0.75    inference(ennf_transformation,[],[f11])).
% 2.81/0.75  fof(f11,negated_conjecture,(
% 2.81/0.75    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.81/0.75    inference(negated_conjecture,[],[f10])).
% 2.81/0.75  fof(f10,conjecture,(
% 2.81/0.75    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.81/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 2.81/0.75  fof(f3085,plain,(
% 2.81/0.75    r1_tarski(sK0,sK1)),
% 2.81/0.75    inference(superposition,[],[f23,f3067])).
% 2.81/0.75  fof(f3067,plain,(
% 2.81/0.75    sK1 = k2_xboole_0(sK0,sK1)),
% 2.81/0.75    inference(backward_demodulation,[],[f2567,f2897])).
% 2.81/0.75  fof(f2897,plain,(
% 2.81/0.75    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X5,X5)) = X4) )),
% 2.81/0.75    inference(superposition,[],[f102,f2449])).
% 2.81/0.75  fof(f2449,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1)) )),
% 2.81/0.75    inference(superposition,[],[f1785,f1785])).
% 2.81/0.75  fof(f1785,plain,(
% 2.81/0.75    ( ! [X16] : (k4_xboole_0(X16,X16) = k4_xboole_0(sK0,sK1)) )),
% 2.81/0.75    inference(resolution,[],[f1771,f661])).
% 2.81/0.75  fof(f661,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r2_hidden(sK5(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 2.81/0.75    inference(duplicate_literal_removal,[],[f658])).
% 2.81/0.75  fof(f658,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r2_hidden(sK5(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1 | r2_hidden(sK5(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 2.81/0.75    inference(resolution,[],[f39,f38])).
% 2.81/0.75  fof(f38,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.81/0.75    inference(cnf_transformation,[],[f3])).
% 2.81/0.75  fof(f3,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.81/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.81/0.75  fof(f39,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.81/0.75    inference(cnf_transformation,[],[f3])).
% 2.81/0.75  fof(f1771,plain,(
% 2.81/0.75    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,sK1))) )),
% 2.81/0.75    inference(subsumption_resolution,[],[f1768,f45])).
% 2.81/0.75  fof(f45,plain,(
% 2.81/0.75    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 2.81/0.75    inference(equality_resolution,[],[f40])).
% 2.81/0.75  fof(f40,plain,(
% 2.81/0.75    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.81/0.75    inference(cnf_transformation,[],[f3])).
% 2.81/0.75  fof(f1768,plain,(
% 2.81/0.75    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k4_xboole_0(sK0,sK1))) )),
% 2.81/0.75    inference(resolution,[],[f1761,f26])).
% 2.81/0.75  fof(f26,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f15])).
% 2.81/0.75  fof(f15,plain,(
% 2.81/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.81/0.75    inference(ennf_transformation,[],[f12])).
% 2.81/0.75  fof(f12,plain,(
% 2.81/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.81/0.75    inference(rectify,[],[f5])).
% 2.81/0.75  fof(f5,axiom,(
% 2.81/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.81/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.81/0.75  fof(f1761,plain,(
% 2.81/0.75    r1_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 2.81/0.75    inference(resolution,[],[f1751,f1324])).
% 2.81/0.75  fof(f1324,plain,(
% 2.81/0.75    ( ! [X28] : (~r1_xboole_0(k4_xboole_0(X28,sK1),sK2) | r1_xboole_0(k4_xboole_0(X28,sK1),sK0)) )),
% 2.81/0.75    inference(resolution,[],[f1307,f255])).
% 2.81/0.75  fof(f255,plain,(
% 2.81/0.75    ( ! [X6] : (~r1_xboole_0(X6,sK1) | ~r1_xboole_0(X6,sK2) | r1_xboole_0(X6,sK0)) )),
% 2.81/0.75    inference(resolution,[],[f36,f66])).
% 2.81/0.75  fof(f66,plain,(
% 2.81/0.75    ( ! [X8] : (~r1_xboole_0(X8,k2_xboole_0(sK1,sK2)) | r1_xboole_0(X8,sK0)) )),
% 2.81/0.75    inference(superposition,[],[f34,f52])).
% 2.81/0.75  fof(f52,plain,(
% 2.81/0.75    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.81/0.75    inference(resolution,[],[f29,f20])).
% 2.81/0.75  fof(f20,plain,(
% 2.81/0.75    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.81/0.75    inference(cnf_transformation,[],[f14])).
% 2.81/0.75  fof(f29,plain,(
% 2.81/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.81/0.75    inference(cnf_transformation,[],[f16])).
% 2.81/0.75  fof(f16,plain,(
% 2.81/0.75    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.81/0.75    inference(ennf_transformation,[],[f6])).
% 2.81/0.75  fof(f6,axiom,(
% 2.81/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.81/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.81/0.75  fof(f34,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f19])).
% 2.81/0.75  fof(f19,plain,(
% 2.81/0.75    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.81/0.75    inference(ennf_transformation,[],[f8])).
% 2.81/0.75  fof(f8,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.81/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.81/0.75  fof(f36,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f19])).
% 2.81/0.75  fof(f1307,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.81/0.75    inference(duplicate_literal_removal,[],[f1302])).
% 2.81/0.75  fof(f1302,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1) | r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.81/0.75    inference(resolution,[],[f71,f28])).
% 2.81/0.75  fof(f28,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f15])).
% 2.81/0.75  fof(f71,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (~r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X1) | r1_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 2.81/0.75    inference(resolution,[],[f44,f27])).
% 2.81/0.75  fof(f27,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f15])).
% 2.81/0.75  fof(f44,plain,(
% 2.81/0.75    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 2.81/0.75    inference(equality_resolution,[],[f41])).
% 2.81/0.75  fof(f41,plain,(
% 2.81/0.75    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.81/0.75    inference(cnf_transformation,[],[f3])).
% 2.81/0.75  fof(f1751,plain,(
% 2.81/0.75    ( ! [X14] : (r1_xboole_0(k4_xboole_0(sK0,X14),sK2)) )),
% 2.81/0.75    inference(duplicate_literal_removal,[],[f1727])).
% 2.81/0.75  fof(f1727,plain,(
% 2.81/0.75    ( ! [X14] : (r1_xboole_0(k4_xboole_0(sK0,X14),sK2) | r1_xboole_0(k4_xboole_0(sK0,X14),sK2)) )),
% 2.81/0.75    inference(resolution,[],[f74,f142])).
% 2.81/0.75  fof(f142,plain,(
% 2.81/0.75    ( ! [X1] : (~r2_hidden(sK3(X1,sK2),sK0) | r1_xboole_0(X1,sK2)) )),
% 2.81/0.75    inference(resolution,[],[f126,f28])).
% 2.81/0.75  fof(f126,plain,(
% 2.81/0.75    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) )),
% 2.81/0.75    inference(resolution,[],[f26,f21])).
% 2.81/0.75  fof(f21,plain,(
% 2.81/0.75    r1_xboole_0(sK0,sK2)),
% 2.81/0.75    inference(cnf_transformation,[],[f14])).
% 2.81/0.75  fof(f74,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X0) | r1_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 2.81/0.75    inference(resolution,[],[f45,f27])).
% 2.81/0.75  fof(f102,plain,(
% 2.81/0.75    ( ! [X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 2.81/0.75    inference(superposition,[],[f92,f24])).
% 2.81/0.75  fof(f24,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f1])).
% 2.81/0.75  fof(f1,axiom,(
% 2.81/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.81/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.81/0.75  fof(f92,plain,(
% 2.81/0.75    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0) )),
% 2.81/0.75    inference(resolution,[],[f88,f29])).
% 2.81/0.75  fof(f88,plain,(
% 2.81/0.75    ( ! [X4] : (r1_tarski(k4_xboole_0(X4,X4),X4)) )),
% 2.81/0.75    inference(superposition,[],[f83,f60])).
% 2.81/0.75  fof(f60,plain,(
% 2.81/0.75    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.81/0.75    inference(resolution,[],[f59,f29])).
% 2.81/0.75  fof(f59,plain,(
% 2.81/0.75    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.81/0.75    inference(duplicate_literal_removal,[],[f58])).
% 2.81/0.75  fof(f58,plain,(
% 2.81/0.75    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 2.81/0.75    inference(resolution,[],[f33,f32])).
% 2.81/0.75  fof(f32,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f18])).
% 2.81/0.75  fof(f18,plain,(
% 2.81/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.81/0.75    inference(ennf_transformation,[],[f2])).
% 2.81/0.75  fof(f2,axiom,(
% 2.81/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.81/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.81/0.75  fof(f33,plain,(
% 2.81/0.75    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f18])).
% 2.81/0.75  fof(f83,plain,(
% 2.81/0.75    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 2.81/0.75    inference(superposition,[],[f48,f25])).
% 2.81/0.75  fof(f25,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f7])).
% 2.81/0.75  fof(f7,axiom,(
% 2.81/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.81/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.81/0.75  fof(f48,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 2.81/0.75    inference(superposition,[],[f23,f24])).
% 2.81/0.75  fof(f2567,plain,(
% 2.81/0.75    ( ! [X15] : (k2_xboole_0(sK1,k4_xboole_0(X15,X15)) = k2_xboole_0(sK0,sK1)) )),
% 2.81/0.75    inference(forward_demodulation,[],[f2528,f24])).
% 2.81/0.75  fof(f2528,plain,(
% 2.81/0.75    ( ! [X15] : (k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k4_xboole_0(X15,X15))) )),
% 2.81/0.75    inference(superposition,[],[f25,f1785])).
% 2.81/0.75  fof(f23,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f9])).
% 2.81/0.75  fof(f9,axiom,(
% 2.81/0.75    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.81/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.81/0.75  % SZS output end Proof for theBenchmark
% 2.81/0.75  % (9542)------------------------------
% 2.81/0.75  % (9542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.75  % (9542)Termination reason: Refutation
% 2.81/0.75  
% 2.81/0.75  % (9542)Memory used [KB]: 8187
% 2.81/0.75  % (9542)Time elapsed: 0.237 s
% 2.81/0.75  % (9542)------------------------------
% 2.81/0.75  % (9542)------------------------------
% 2.81/0.76  % (9535)Success in time 0.389 s
%------------------------------------------------------------------------------
