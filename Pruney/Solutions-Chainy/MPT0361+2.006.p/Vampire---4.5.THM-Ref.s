%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:59 EST 2020

% Result     : Theorem 5.06s
% Output     : Refutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 131 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   19
%              Number of atoms          :  124 ( 254 expanded)
%              Number of equality atoms :   31 (  57 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10842,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10841,f2226])).

fof(f2226,plain,(
    ! [X12,X10,X11] : r1_tarski(k4_xboole_0(X10,k2_xboole_0(X11,X12)),k4_xboole_0(X10,X11)) ),
    inference(superposition,[],[f33,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f10841,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f7813,f10837])).

fof(f10837,plain,(
    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f10835,f9346])).

fof(f9346,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(resolution,[],[f396,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f396,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X2))
      | k4_xboole_0(X2,X3) = k3_subset_1(X2,X3) ) ),
    inference(subsumption_resolution,[],[f394,f31])).

fof(f31,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f394,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X3) = k3_subset_1(X2,X3)
      | ~ r2_hidden(X3,k1_zfmisc_1(X2))
      | v1_xboole_0(k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f10835,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f10822,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f10822,plain,(
    r1_tarski(k2_xboole_0(sK2,sK1),sK0) ),
    inference(superposition,[],[f10764,f77])).

fof(f77,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f41,f72])).

fof(f72,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f66,f31])).

fof(f66,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f10764,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0)) ),
    inference(forward_demodulation,[],[f10763,f74])).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f10763,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK0))) ),
    inference(forward_demodulation,[],[f10735,f35])).

fof(f10735,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0)) ),
    inference(resolution,[],[f10681,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f10681,plain,(
    ! [X18] : r1_tarski(k4_xboole_0(k2_xboole_0(X18,sK1),k2_xboole_0(X18,sK0)),k1_xboole_0) ),
    inference(superposition,[],[f3974,f118])).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f60,f74])).

fof(f60,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f34,f35])).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f3974,plain,(
    ! [X4,X3] : r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,sK0)),k4_xboole_0(X3,k2_xboole_0(X4,sK1))) ),
    inference(forward_demodulation,[],[f3969,f52])).

fof(f3969,plain,(
    ! [X4,X3] : r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,sK0)),k4_xboole_0(k4_xboole_0(X3,X4),sK1)) ),
    inference(superposition,[],[f3840,f52])).

fof(f3840,plain,(
    ! [X51] : r1_tarski(k4_xboole_0(X51,sK0),k4_xboole_0(X51,sK1)) ),
    inference(superposition,[],[f2226,f78])).

fof(f78,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f41,f73])).

fof(f73,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f71,f57])).

fof(f71,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f67,f31])).

fof(f67,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f7813,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f395,f7807])).

fof(f7807,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f5728,f30])).

fof(f5728,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2) ) ),
    inference(resolution,[],[f54,f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f395,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f29,f392])).

fof(f392,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f43,f30])).

fof(f29,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:16:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (21455)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.49  % (21434)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (21435)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (21460)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (21457)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (21443)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (21449)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (21442)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (21447)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (21448)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (21446)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (21441)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (21459)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (21437)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (21439)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (21444)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (21450)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (21451)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (21436)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (21445)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % (21458)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (21440)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (21452)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.55  % (21453)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.55  % (21454)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.56  % (21456)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 2.30/0.66  % (21444)Refutation not found, incomplete strategy% (21444)------------------------------
% 2.30/0.66  % (21444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.66  % (21444)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.66  
% 2.30/0.66  % (21444)Memory used [KB]: 6140
% 2.30/0.66  % (21444)Time elapsed: 0.237 s
% 2.30/0.66  % (21444)------------------------------
% 2.30/0.66  % (21444)------------------------------
% 4.14/0.91  % (21448)Time limit reached!
% 4.14/0.91  % (21448)------------------------------
% 4.14/0.91  % (21448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.91  % (21448)Termination reason: Time limit
% 4.14/0.91  % (21448)Termination phase: Saturation
% 4.14/0.91  
% 4.14/0.91  % (21448)Memory used [KB]: 10106
% 4.14/0.91  % (21448)Time elapsed: 0.500 s
% 4.14/0.91  % (21448)------------------------------
% 4.14/0.91  % (21448)------------------------------
% 4.14/0.91  % (21434)Time limit reached!
% 4.14/0.91  % (21434)------------------------------
% 4.14/0.91  % (21434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.91  % (21434)Termination reason: Time limit
% 4.14/0.91  % (21434)Termination phase: Saturation
% 4.14/0.91  
% 4.14/0.91  % (21434)Memory used [KB]: 16502
% 4.14/0.91  % (21434)Time elapsed: 0.500 s
% 4.14/0.91  % (21434)------------------------------
% 4.14/0.91  % (21434)------------------------------
% 4.58/0.95  % (21449)Time limit reached!
% 4.58/0.95  % (21449)------------------------------
% 4.58/0.95  % (21449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/0.95  % (21449)Termination reason: Time limit
% 4.58/0.95  
% 4.58/0.95  % (21449)Memory used [KB]: 7419
% 4.58/0.95  % (21449)Time elapsed: 0.508 s
% 4.58/0.95  % (21449)------------------------------
% 4.58/0.95  % (21449)------------------------------
% 5.06/1.03  % (21454)Refutation found. Thanks to Tanya!
% 5.06/1.03  % SZS status Theorem for theBenchmark
% 5.06/1.03  % SZS output start Proof for theBenchmark
% 5.06/1.03  fof(f10842,plain,(
% 5.06/1.03    $false),
% 5.06/1.03    inference(subsumption_resolution,[],[f10841,f2226])).
% 5.06/1.03  fof(f2226,plain,(
% 5.06/1.03    ( ! [X12,X10,X11] : (r1_tarski(k4_xboole_0(X10,k2_xboole_0(X11,X12)),k4_xboole_0(X10,X11))) )),
% 5.06/1.03    inference(superposition,[],[f33,f52])).
% 5.06/1.03  fof(f52,plain,(
% 5.06/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.06/1.03    inference(cnf_transformation,[],[f7])).
% 5.06/1.03  fof(f7,axiom,(
% 5.06/1.03    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 5.06/1.03  fof(f33,plain,(
% 5.06/1.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.06/1.03    inference(cnf_transformation,[],[f5])).
% 5.06/1.03  fof(f5,axiom,(
% 5.06/1.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 5.06/1.03  fof(f10841,plain,(
% 5.06/1.03    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 5.06/1.03    inference(backward_demodulation,[],[f7813,f10837])).
% 5.06/1.03  fof(f10837,plain,(
% 5.06/1.03    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 5.06/1.03    inference(resolution,[],[f10835,f9346])).
% 5.06/1.03  fof(f9346,plain,(
% 5.06/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 5.06/1.03    inference(resolution,[],[f396,f58])).
% 5.06/1.03  fof(f58,plain,(
% 5.06/1.03    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 5.06/1.03    inference(equality_resolution,[],[f48])).
% 5.06/1.03  fof(f48,plain,(
% 5.06/1.03    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 5.06/1.03    inference(cnf_transformation,[],[f10])).
% 5.06/1.03  fof(f10,axiom,(
% 5.06/1.03    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 5.06/1.03  fof(f396,plain,(
% 5.06/1.03    ( ! [X2,X3] : (~r2_hidden(X3,k1_zfmisc_1(X2)) | k4_xboole_0(X2,X3) = k3_subset_1(X2,X3)) )),
% 5.06/1.03    inference(subsumption_resolution,[],[f394,f31])).
% 5.06/1.03  fof(f31,plain,(
% 5.06/1.03    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 5.06/1.03    inference(cnf_transformation,[],[f14])).
% 5.06/1.03  fof(f14,axiom,(
% 5.06/1.03    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 5.06/1.03  fof(f394,plain,(
% 5.06/1.03    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_subset_1(X2,X3) | ~r2_hidden(X3,k1_zfmisc_1(X2)) | v1_xboole_0(k1_zfmisc_1(X2))) )),
% 5.06/1.03    inference(resolution,[],[f43,f39])).
% 5.06/1.03  fof(f39,plain,(
% 5.06/1.03    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 5.06/1.03    inference(cnf_transformation,[],[f20])).
% 5.06/1.03  fof(f20,plain,(
% 5.06/1.03    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 5.06/1.03    inference(ennf_transformation,[],[f11])).
% 5.06/1.03  fof(f11,axiom,(
% 5.06/1.03    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 5.06/1.03  fof(f43,plain,(
% 5.06/1.03    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 5.06/1.03    inference(cnf_transformation,[],[f23])).
% 5.06/1.03  fof(f23,plain,(
% 5.06/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.06/1.03    inference(ennf_transformation,[],[f12])).
% 5.06/1.03  fof(f12,axiom,(
% 5.06/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 5.06/1.03  fof(f10835,plain,(
% 5.06/1.03    r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 5.06/1.03    inference(forward_demodulation,[],[f10822,f35])).
% 5.06/1.03  fof(f35,plain,(
% 5.06/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.06/1.03    inference(cnf_transformation,[],[f1])).
% 5.06/1.03  fof(f1,axiom,(
% 5.06/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.06/1.03  fof(f10822,plain,(
% 5.06/1.03    r1_tarski(k2_xboole_0(sK2,sK1),sK0)),
% 5.06/1.03    inference(superposition,[],[f10764,f77])).
% 5.06/1.03  fof(f77,plain,(
% 5.06/1.03    sK0 = k2_xboole_0(sK2,sK0)),
% 5.06/1.03    inference(resolution,[],[f41,f72])).
% 5.06/1.03  fof(f72,plain,(
% 5.06/1.03    r1_tarski(sK2,sK0)),
% 5.06/1.03    inference(resolution,[],[f70,f57])).
% 5.06/1.03  fof(f57,plain,(
% 5.06/1.03    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 5.06/1.03    inference(equality_resolution,[],[f49])).
% 5.06/1.03  fof(f49,plain,(
% 5.06/1.03    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 5.06/1.03    inference(cnf_transformation,[],[f10])).
% 5.06/1.03  fof(f70,plain,(
% 5.06/1.03    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 5.06/1.03    inference(subsumption_resolution,[],[f66,f31])).
% 5.06/1.03  fof(f66,plain,(
% 5.06/1.03    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 5.06/1.03    inference(resolution,[],[f40,f28])).
% 5.06/1.03  fof(f28,plain,(
% 5.06/1.03    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 5.06/1.03    inference(cnf_transformation,[],[f19])).
% 5.06/1.03  fof(f19,plain,(
% 5.06/1.03    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.06/1.03    inference(ennf_transformation,[],[f18])).
% 5.06/1.03  fof(f18,negated_conjecture,(
% 5.06/1.03    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 5.06/1.03    inference(negated_conjecture,[],[f17])).
% 5.06/1.03  fof(f17,conjecture,(
% 5.06/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 5.06/1.03  fof(f40,plain,(
% 5.06/1.03    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 5.06/1.03    inference(cnf_transformation,[],[f20])).
% 5.06/1.03  fof(f41,plain,(
% 5.06/1.03    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 5.06/1.03    inference(cnf_transformation,[],[f21])).
% 5.06/1.03  fof(f21,plain,(
% 5.06/1.03    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 5.06/1.03    inference(ennf_transformation,[],[f3])).
% 5.06/1.03  fof(f3,axiom,(
% 5.06/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 5.06/1.03  fof(f10764,plain,(
% 5.06/1.03    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0))) )),
% 5.06/1.03    inference(forward_demodulation,[],[f10763,f74])).
% 5.06/1.03  fof(f74,plain,(
% 5.06/1.03    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.06/1.03    inference(resolution,[],[f41,f32])).
% 5.06/1.03  fof(f32,plain,(
% 5.06/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 5.06/1.03    inference(cnf_transformation,[],[f4])).
% 5.06/1.03  fof(f4,axiom,(
% 5.06/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 5.06/1.03  fof(f10763,plain,(
% 5.06/1.03    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK0)))) )),
% 5.06/1.03    inference(forward_demodulation,[],[f10735,f35])).
% 5.06/1.03  fof(f10735,plain,(
% 5.06/1.03    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0))) )),
% 5.06/1.03    inference(resolution,[],[f10681,f53])).
% 5.06/1.03  fof(f53,plain,(
% 5.06/1.03    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 5.06/1.03    inference(cnf_transformation,[],[f25])).
% 5.06/1.03  fof(f25,plain,(
% 5.06/1.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 5.06/1.03    inference(ennf_transformation,[],[f8])).
% 5.06/1.03  fof(f8,axiom,(
% 5.06/1.03    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 5.06/1.03  fof(f10681,plain,(
% 5.06/1.03    ( ! [X18] : (r1_tarski(k4_xboole_0(k2_xboole_0(X18,sK1),k2_xboole_0(X18,sK0)),k1_xboole_0)) )),
% 5.06/1.03    inference(superposition,[],[f3974,f118])).
% 5.06/1.03  fof(f118,plain,(
% 5.06/1.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 5.06/1.03    inference(superposition,[],[f60,f74])).
% 5.06/1.03  fof(f60,plain,(
% 5.06/1.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 5.06/1.03    inference(superposition,[],[f34,f35])).
% 5.06/1.03  fof(f34,plain,(
% 5.06/1.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 5.06/1.03    inference(cnf_transformation,[],[f9])).
% 5.06/1.03  fof(f9,axiom,(
% 5.06/1.03    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 5.06/1.03  fof(f3974,plain,(
% 5.06/1.03    ( ! [X4,X3] : (r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,sK0)),k4_xboole_0(X3,k2_xboole_0(X4,sK1)))) )),
% 5.06/1.03    inference(forward_demodulation,[],[f3969,f52])).
% 5.06/1.03  fof(f3969,plain,(
% 5.06/1.03    ( ! [X4,X3] : (r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,sK0)),k4_xboole_0(k4_xboole_0(X3,X4),sK1))) )),
% 5.06/1.03    inference(superposition,[],[f3840,f52])).
% 5.06/1.03  fof(f3840,plain,(
% 5.06/1.03    ( ! [X51] : (r1_tarski(k4_xboole_0(X51,sK0),k4_xboole_0(X51,sK1))) )),
% 5.06/1.03    inference(superposition,[],[f2226,f78])).
% 5.06/1.03  fof(f78,plain,(
% 5.06/1.03    sK0 = k2_xboole_0(sK1,sK0)),
% 5.06/1.03    inference(resolution,[],[f41,f73])).
% 5.06/1.03  fof(f73,plain,(
% 5.06/1.03    r1_tarski(sK1,sK0)),
% 5.06/1.03    inference(resolution,[],[f71,f57])).
% 5.06/1.03  fof(f71,plain,(
% 5.06/1.03    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 5.06/1.03    inference(subsumption_resolution,[],[f67,f31])).
% 5.06/1.03  fof(f67,plain,(
% 5.06/1.03    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 5.06/1.03    inference(resolution,[],[f40,f30])).
% 5.06/1.03  fof(f30,plain,(
% 5.06/1.03    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 5.06/1.03    inference(cnf_transformation,[],[f19])).
% 5.06/1.03  fof(f7813,plain,(
% 5.06/1.03    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 5.06/1.03    inference(backward_demodulation,[],[f395,f7807])).
% 5.06/1.03  fof(f7807,plain,(
% 5.06/1.03    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 5.06/1.03    inference(resolution,[],[f5728,f30])).
% 5.06/1.03  fof(f5728,plain,(
% 5.06/1.03    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2)) )),
% 5.06/1.03    inference(resolution,[],[f54,f28])).
% 5.06/1.03  fof(f54,plain,(
% 5.06/1.03    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 5.06/1.03    inference(cnf_transformation,[],[f27])).
% 5.06/1.03  fof(f27,plain,(
% 5.06/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.06/1.03    inference(flattening,[],[f26])).
% 5.06/1.03  fof(f26,plain,(
% 5.06/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.06/1.03    inference(ennf_transformation,[],[f16])).
% 5.06/1.03  fof(f16,axiom,(
% 5.06/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 5.06/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 5.06/1.03  fof(f395,plain,(
% 5.06/1.03    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 5.06/1.03    inference(backward_demodulation,[],[f29,f392])).
% 5.06/1.03  fof(f392,plain,(
% 5.06/1.03    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 5.06/1.03    inference(resolution,[],[f43,f30])).
% 5.06/1.03  fof(f29,plain,(
% 5.06/1.03    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 5.06/1.03    inference(cnf_transformation,[],[f19])).
% 5.06/1.03  % SZS output end Proof for theBenchmark
% 5.06/1.03  % (21454)------------------------------
% 5.06/1.03  % (21454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.06/1.03  % (21454)Termination reason: Refutation
% 5.06/1.03  
% 5.06/1.03  % (21454)Memory used [KB]: 6908
% 5.06/1.03  % (21454)Time elapsed: 0.626 s
% 5.06/1.03  % (21454)------------------------------
% 5.06/1.03  % (21454)------------------------------
% 5.41/1.05  % (21432)Success in time 0.689 s
%------------------------------------------------------------------------------
