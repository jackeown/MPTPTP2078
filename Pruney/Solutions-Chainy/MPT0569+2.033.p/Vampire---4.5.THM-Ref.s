%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:31 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 122 expanded)
%              Number of leaves         :    7 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  134 ( 355 expanded)
%              Number of equality atoms :   23 (  66 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(subsumption_resolution,[],[f387,f148])).

fof(f148,plain,(
    ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f147])).

fof(f147,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f15,f146])).

fof(f146,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(resolution,[],[f135,f59])).

fof(f59,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3,k1_xboole_0),X3)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f21,f39])).

fof(f39,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f17,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f17,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f135,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,sK0))
      | k1_xboole_0 = k10_relat_1(sK1,sK0) ) ),
    inference(resolution,[],[f134,f14])).

fof(f14,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(sK1),X1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | ~ r1_xboole_0(k2_relat_1(sK1),X1) ) ),
    inference(resolution,[],[f129,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,sK1),X2)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | ~ r1_xboole_0(X2,X1) ) ),
    inference(resolution,[],[f103,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,sK1),X1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f32,f16])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f129,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,sK1),k2_relat_1(sK1))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f30,f16])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f387,plain,(
    r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f386,f39])).

fof(f386,plain,
    ( r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(superposition,[],[f380,f146])).

fof(f380,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),X1)),k10_relat_1(sK1,X1))
      | r1_xboole_0(k2_relat_1(sK1),X1) ) ),
    inference(duplicate_literal_removal,[],[f377])).

fof(f377,plain,(
    ! [X1] :
      ( r1_xboole_0(k2_relat_1(sK1),X1)
      | r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),X1)),k10_relat_1(sK1,X1))
      | r1_xboole_0(k2_relat_1(sK1),X1) ) ),
    inference(resolution,[],[f368,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f368,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(k2_relat_1(sK1),X2),X3)
      | r1_xboole_0(k2_relat_1(sK1),X2)
      | r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),X2)),k10_relat_1(sK1,X3)) ) ),
    inference(resolution,[],[f47,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,k10_relat_1(sK1,X2)) ) ),
    inference(resolution,[],[f38,f16])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f33,f35])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,sK2(k2_relat_1(X0),X1)),sK2(k2_relat_1(X0),X1)),X0)
      | r1_xboole_0(k2_relat_1(X0),X1) ) ),
    inference(resolution,[],[f34,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (15371)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (15374)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.15/0.51  % (15390)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.15/0.51  % (15386)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.15/0.52  % (15381)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.15/0.52  % (15376)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.15/0.52  % (15388)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.52  % (15377)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.52  % (15379)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.53  % (15373)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (15385)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.53  % (15394)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.53  % (15387)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.53  % (15370)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.54  % (15372)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (15383)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.54  % (15378)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.55  % (15376)Refutation found. Thanks to Tanya!
% 1.29/0.55  % SZS status Theorem for theBenchmark
% 1.29/0.55  % SZS output start Proof for theBenchmark
% 1.29/0.55  fof(f388,plain,(
% 1.29/0.55    $false),
% 1.29/0.55    inference(subsumption_resolution,[],[f387,f148])).
% 1.29/0.55  fof(f148,plain,(
% 1.29/0.55    ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.29/0.55    inference(trivial_inequality_removal,[],[f147])).
% 1.29/0.55  fof(f147,plain,(
% 1.29/0.55    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.29/0.55    inference(backward_demodulation,[],[f15,f146])).
% 1.29/0.55  fof(f146,plain,(
% 1.29/0.55    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.29/0.55    inference(duplicate_literal_removal,[],[f142])).
% 1.29/0.55  fof(f142,plain,(
% 1.29/0.55    k1_xboole_0 = k10_relat_1(sK1,sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.29/0.55    inference(resolution,[],[f135,f59])).
% 1.29/0.55  fof(f59,plain,(
% 1.29/0.55    ( ! [X3] : (r2_hidden(sK3(X3,k1_xboole_0),X3) | k1_xboole_0 = X3) )),
% 1.29/0.55    inference(resolution,[],[f21,f39])).
% 1.29/0.55  fof(f39,plain,(
% 1.29/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.29/0.55    inference(superposition,[],[f17,f36])).
% 1.29/0.55  fof(f36,plain,(
% 1.29/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.29/0.55    inference(equality_resolution,[],[f29])).
% 1.29/0.55  fof(f29,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.29/0.55    inference(cnf_transformation,[],[f3])).
% 1.29/0.55  fof(f3,axiom,(
% 1.29/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.29/0.55  fof(f17,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f4])).
% 1.29/0.55  fof(f4,axiom,(
% 1.29/0.55    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.29/0.55  fof(f21,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 1.29/0.55    inference(cnf_transformation,[],[f12])).
% 1.29/0.55  fof(f12,plain,(
% 1.29/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.29/0.55    inference(ennf_transformation,[],[f1])).
% 1.29/0.55  fof(f1,axiom,(
% 1.29/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.29/0.55  fof(f135,plain,(
% 1.29/0.55    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,sK0)) | k1_xboole_0 = k10_relat_1(sK1,sK0)) )),
% 1.29/0.55    inference(resolution,[],[f134,f14])).
% 1.29/0.55  fof(f14,plain,(
% 1.29/0.55    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.29/0.55    inference(cnf_transformation,[],[f10])).
% 1.29/0.55  fof(f10,plain,(
% 1.29/0.55    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f8])).
% 1.29/0.55  fof(f8,negated_conjecture,(
% 1.29/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.29/0.55    inference(negated_conjecture,[],[f7])).
% 1.29/0.55  fof(f7,conjecture,(
% 1.29/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.29/0.55  fof(f134,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(sK1),X1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 1.29/0.55    inference(duplicate_literal_removal,[],[f131])).
% 1.29/0.55  fof(f131,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | ~r2_hidden(X0,k10_relat_1(sK1,X1)) | ~r1_xboole_0(k2_relat_1(sK1),X1)) )),
% 1.29/0.55    inference(resolution,[],[f129,f104])).
% 1.29/0.55  fof(f104,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,sK1),X2) | ~r2_hidden(X0,k10_relat_1(sK1,X1)) | ~r1_xboole_0(X2,X1)) )),
% 1.29/0.55    inference(resolution,[],[f103,f18])).
% 1.29/0.55  fof(f18,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f11])).
% 1.29/0.55  fof(f11,plain,(
% 1.29/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.29/0.55    inference(ennf_transformation,[],[f9])).
% 1.29/0.55  fof(f9,plain,(
% 1.29/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.29/0.55    inference(rectify,[],[f2])).
% 1.29/0.55  fof(f2,axiom,(
% 1.29/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.29/0.55  fof(f103,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,sK1),X1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 1.29/0.55    inference(resolution,[],[f32,f16])).
% 1.29/0.55  fof(f16,plain,(
% 1.29/0.55    v1_relat_1(sK1)),
% 1.29/0.55    inference(cnf_transformation,[],[f10])).
% 1.29/0.55  fof(f32,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f13])).
% 1.29/0.55  fof(f13,plain,(
% 1.29/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.29/0.55    inference(ennf_transformation,[],[f6])).
% 1.29/0.55  fof(f6,axiom,(
% 1.29/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.29/0.55  fof(f129,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,sK1),k2_relat_1(sK1)) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 1.29/0.55    inference(resolution,[],[f30,f16])).
% 1.29/0.55  fof(f30,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f13])).
% 1.29/0.55  fof(f15,plain,(
% 1.29/0.55    k1_xboole_0 != k10_relat_1(sK1,sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.29/0.55    inference(cnf_transformation,[],[f10])).
% 1.29/0.55  fof(f387,plain,(
% 1.29/0.55    r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.29/0.55    inference(subsumption_resolution,[],[f386,f39])).
% 1.29/0.55  fof(f386,plain,(
% 1.29/0.55    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0) | r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.29/0.55    inference(superposition,[],[f380,f146])).
% 1.29/0.55  fof(f380,plain,(
% 1.29/0.55    ( ! [X1] : (r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),X1)),k10_relat_1(sK1,X1)) | r1_xboole_0(k2_relat_1(sK1),X1)) )),
% 1.29/0.55    inference(duplicate_literal_removal,[],[f377])).
% 1.29/0.55  fof(f377,plain,(
% 1.29/0.55    ( ! [X1] : (r1_xboole_0(k2_relat_1(sK1),X1) | r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),X1)),k10_relat_1(sK1,X1)) | r1_xboole_0(k2_relat_1(sK1),X1)) )),
% 1.29/0.55    inference(resolution,[],[f368,f20])).
% 1.29/0.55  fof(f20,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f11])).
% 1.29/0.55  fof(f368,plain,(
% 1.29/0.55    ( ! [X2,X3] : (~r2_hidden(sK2(k2_relat_1(sK1),X2),X3) | r1_xboole_0(k2_relat_1(sK1),X2) | r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),X2)),k10_relat_1(sK1,X3))) )),
% 1.29/0.55    inference(resolution,[],[f47,f155])).
% 1.29/0.55  fof(f155,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X1,X2) | r2_hidden(X0,k10_relat_1(sK1,X2))) )),
% 1.29/0.55    inference(resolution,[],[f38,f16])).
% 1.29/0.55  fof(f38,plain,(
% 1.29/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.29/0.55    inference(subsumption_resolution,[],[f33,f35])).
% 1.29/0.55  fof(f35,plain,(
% 1.29/0.55    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 1.29/0.55    inference(equality_resolution,[],[f23])).
% 1.29/0.55  fof(f23,plain,(
% 1.29/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.29/0.55    inference(cnf_transformation,[],[f5])).
% 1.29/0.55  fof(f5,axiom,(
% 1.29/0.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.29/0.55  fof(f33,plain,(
% 1.29/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f13])).
% 1.29/0.55  fof(f47,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,sK2(k2_relat_1(X0),X1)),sK2(k2_relat_1(X0),X1)),X0) | r1_xboole_0(k2_relat_1(X0),X1)) )),
% 1.29/0.55    inference(resolution,[],[f34,f19])).
% 1.29/0.55  fof(f19,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f11])).
% 1.29/0.55  fof(f34,plain,(
% 1.29/0.55    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)) )),
% 1.29/0.55    inference(equality_resolution,[],[f24])).
% 1.29/0.55  fof(f24,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.29/0.55    inference(cnf_transformation,[],[f5])).
% 1.29/0.55  % SZS output end Proof for theBenchmark
% 1.29/0.55  % (15376)------------------------------
% 1.29/0.55  % (15376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (15376)Termination reason: Refutation
% 1.29/0.55  
% 1.29/0.55  % (15376)Memory used [KB]: 6524
% 1.29/0.55  % (15376)Time elapsed: 0.139 s
% 1.29/0.55  % (15376)------------------------------
% 1.29/0.55  % (15376)------------------------------
% 1.29/0.55  % (15393)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.55  % (15378)Refutation not found, incomplete strategy% (15378)------------------------------
% 1.29/0.55  % (15378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (15378)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (15378)Memory used [KB]: 10746
% 1.29/0.55  % (15378)Time elapsed: 0.122 s
% 1.29/0.55  % (15378)------------------------------
% 1.29/0.55  % (15378)------------------------------
% 1.29/0.55  % (15399)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.55  % (15392)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.55  % (15396)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.55  % (15384)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.56  % (15389)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.56  % (15398)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.56  % (15392)Refutation not found, incomplete strategy% (15392)------------------------------
% 1.29/0.56  % (15392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (15392)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (15392)Memory used [KB]: 10746
% 1.29/0.56  % (15392)Time elapsed: 0.116 s
% 1.29/0.56  % (15392)------------------------------
% 1.29/0.56  % (15392)------------------------------
% 1.29/0.56  % (15375)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.56  % (15382)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.57  % (15380)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.57  % (15397)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.57  % (15391)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.57  % (15369)Success in time 0.208 s
%------------------------------------------------------------------------------
