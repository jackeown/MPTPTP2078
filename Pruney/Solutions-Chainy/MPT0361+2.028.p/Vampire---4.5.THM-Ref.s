%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:02 EST 2020

% Result     : Theorem 2.30s
% Output     : Refutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 245 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  126 ( 585 expanded)
%              Number of equality atoms :   14 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f694,plain,(
    $false ),
    inference(global_subsumption,[],[f482,f690])).

fof(f690,plain,(
    sP6(sK3(k2_xboole_0(sK1,sK2),sK0),sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f437,f137])).

fof(f137,plain,(
    ! [X4,X2,X3] :
      ( sP6(sK3(k2_xboole_0(X2,X3),X4),X3,X2)
      | r1_tarski(k2_xboole_0(X2,X3),X4) ) ),
    inference(resolution,[],[f47,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f437,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f431,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(global_subsumption,[],[f22,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f26,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f22,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f431,plain,(
    ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f170,f322])).

fof(f322,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f320,f306])).

fof(f306,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f21,f19,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f320,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f215,f306])).

fof(f215,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f204,f201])).

fof(f201,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f21,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f204,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f20,f28])).

fof(f20,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f170,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f23,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f482,plain,(
    ~ sP6(sK3(k2_xboole_0(sK1,sK2),sK0),sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f457,f458,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f458,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f79,f441,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f441,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f437,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    r1_tarski(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f71,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f22,f19,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f457,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f87,f441,f29])).

fof(f87,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f72,f45])).

fof(f72,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f22,f21,f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (31730)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (31734)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.56  % (31728)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.56  % (31732)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.39/0.56  % (31740)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.56  % (31750)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.56  % (31749)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.57  % (31736)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.57  % (31742)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.57  % (31741)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.64/0.58  % (31744)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.64/0.58  % (31729)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.64/0.58  % (31733)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.64/0.58  % (31748)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.64/0.58  % (31727)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.64/0.59  % (31731)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.64/0.59  % (31754)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.64/0.60  % (31752)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.64/0.60  % (31735)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.64/0.60  % (31746)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.64/0.60  % (31743)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.64/0.60  % (31756)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.64/0.60  % (31747)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.64/0.61  % (31738)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.64/0.61  % (31739)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.64/0.61  % (31738)Refutation not found, incomplete strategy% (31738)------------------------------
% 1.64/0.61  % (31738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (31738)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.61  
% 1.64/0.61  % (31738)Memory used [KB]: 10746
% 1.64/0.61  % (31738)Time elapsed: 0.193 s
% 1.64/0.61  % (31738)------------------------------
% 1.64/0.61  % (31738)------------------------------
% 1.64/0.61  % (31751)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.64/0.62  % (31745)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.64/0.62  % (31755)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.64/0.63  % (31737)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.64/0.63  % (31737)Refutation not found, incomplete strategy% (31737)------------------------------
% 1.64/0.63  % (31737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.63  % (31737)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.63  
% 1.64/0.63  % (31737)Memory used [KB]: 10618
% 1.64/0.63  % (31737)Time elapsed: 0.197 s
% 1.64/0.63  % (31737)------------------------------
% 1.64/0.63  % (31737)------------------------------
% 1.64/0.64  % (31753)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.30/0.67  % (31751)Refutation found. Thanks to Tanya!
% 2.30/0.67  % SZS status Theorem for theBenchmark
% 2.30/0.68  % SZS output start Proof for theBenchmark
% 2.30/0.68  fof(f694,plain,(
% 2.30/0.68    $false),
% 2.30/0.68    inference(global_subsumption,[],[f482,f690])).
% 2.30/0.68  fof(f690,plain,(
% 2.30/0.68    sP6(sK3(k2_xboole_0(sK1,sK2),sK0),sK2,sK1)),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f437,f137])).
% 2.30/0.68  fof(f137,plain,(
% 2.30/0.68    ( ! [X4,X2,X3] : (sP6(sK3(k2_xboole_0(X2,X3),X4),X3,X2) | r1_tarski(k2_xboole_0(X2,X3),X4)) )),
% 2.30/0.68    inference(resolution,[],[f47,f30])).
% 2.30/0.68  fof(f30,plain,(
% 2.30/0.68    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f15])).
% 2.30/0.68  fof(f15,plain,(
% 2.30/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.30/0.68    inference(ennf_transformation,[],[f1])).
% 2.30/0.68  fof(f1,axiom,(
% 2.30/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.30/0.68  fof(f47,plain,(
% 2.30/0.68    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | sP6(X3,X1,X0)) )),
% 2.30/0.68    inference(equality_resolution,[],[f42])).
% 2.30/0.68  fof(f42,plain,(
% 2.30/0.68    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.30/0.68    inference(cnf_transformation,[],[f2])).
% 2.49/0.68  fof(f2,axiom,(
% 2.49/0.68    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.49/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.49/0.68  fof(f437,plain,(
% 2.49/0.68    ~r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 2.49/0.68    inference(unit_resulting_resolution,[],[f431,f65])).
% 2.49/0.68  fof(f65,plain,(
% 2.49/0.68    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 2.49/0.68    inference(global_subsumption,[],[f22,f63])).
% 2.49/0.69  fof(f63,plain,(
% 2.49/0.69    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 2.49/0.69    inference(resolution,[],[f26,f46])).
% 2.49/0.69  fof(f46,plain,(
% 2.49/0.69    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 2.49/0.69    inference(equality_resolution,[],[f32])).
% 2.49/0.69  fof(f32,plain,(
% 2.49/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.49/0.69    inference(cnf_transformation,[],[f5])).
% 2.49/0.69  fof(f5,axiom,(
% 2.49/0.69    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.49/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.49/0.69  fof(f26,plain,(
% 2.49/0.69    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f13])).
% 2.49/0.69  fof(f13,plain,(
% 2.49/0.69    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.49/0.69    inference(ennf_transformation,[],[f6])).
% 2.49/0.69  fof(f6,axiom,(
% 2.49/0.69    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.49/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.49/0.69  fof(f22,plain,(
% 2.49/0.69    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.49/0.69    inference(cnf_transformation,[],[f8])).
% 2.49/0.69  fof(f8,axiom,(
% 2.49/0.69    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.49/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.49/0.69  fof(f431,plain,(
% 2.49/0.69    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f170,f322])).
% 2.49/0.69  fof(f322,plain,(
% 2.49/0.69    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 2.49/0.69    inference(forward_demodulation,[],[f320,f306])).
% 2.49/0.69  fof(f306,plain,(
% 2.49/0.69    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f21,f19,f37])).
% 2.49/0.69  fof(f37,plain,(
% 2.49/0.69    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.49/0.69    inference(cnf_transformation,[],[f18])).
% 2.49/0.69  fof(f18,plain,(
% 2.49/0.69    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.49/0.69    inference(flattening,[],[f17])).
% 2.49/0.69  fof(f17,plain,(
% 2.49/0.69    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.49/0.69    inference(ennf_transformation,[],[f9])).
% 2.49/0.69  fof(f9,axiom,(
% 2.49/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.49/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.49/0.69  fof(f19,plain,(
% 2.49/0.69    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.49/0.69    inference(cnf_transformation,[],[f12])).
% 2.49/0.69  fof(f12,plain,(
% 2.49/0.69    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.49/0.69    inference(ennf_transformation,[],[f11])).
% 2.49/0.69  fof(f11,negated_conjecture,(
% 2.49/0.69    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.49/0.69    inference(negated_conjecture,[],[f10])).
% 2.49/0.69  fof(f10,conjecture,(
% 2.49/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.49/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 2.49/0.69  fof(f21,plain,(
% 2.49/0.69    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.49/0.69    inference(cnf_transformation,[],[f12])).
% 2.49/0.69  fof(f320,plain,(
% 2.49/0.69    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 2.49/0.69    inference(backward_demodulation,[],[f215,f306])).
% 2.49/0.69  fof(f215,plain,(
% 2.49/0.69    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 2.49/0.69    inference(forward_demodulation,[],[f204,f201])).
% 2.49/0.69  fof(f201,plain,(
% 2.49/0.69    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f21,f28])).
% 2.49/0.69  fof(f28,plain,(
% 2.49/0.69    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.49/0.69    inference(cnf_transformation,[],[f14])).
% 2.49/0.69  fof(f14,plain,(
% 2.49/0.69    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.49/0.69    inference(ennf_transformation,[],[f7])).
% 2.49/0.69  fof(f7,axiom,(
% 2.49/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 2.49/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.49/0.69  fof(f204,plain,(
% 2.49/0.69    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) | ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 2.49/0.69    inference(superposition,[],[f20,f28])).
% 2.49/0.69  fof(f20,plain,(
% 2.49/0.69    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 2.49/0.69    inference(cnf_transformation,[],[f12])).
% 2.49/0.69  fof(f170,plain,(
% 2.49/0.69    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f23,f36])).
% 2.49/0.69  fof(f36,plain,(
% 2.49/0.69    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f16])).
% 2.49/0.69  fof(f16,plain,(
% 2.49/0.69    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 2.49/0.69    inference(ennf_transformation,[],[f3])).
% 2.49/0.69  fof(f3,axiom,(
% 2.49/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 2.49/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 2.49/0.69  fof(f23,plain,(
% 2.49/0.69    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.49/0.69    inference(cnf_transformation,[],[f4])).
% 2.49/0.69  fof(f4,axiom,(
% 2.49/0.69    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.49/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.49/0.69  fof(f482,plain,(
% 2.49/0.69    ~sP6(sK3(k2_xboole_0(sK1,sK2),sK0),sK2,sK1)),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f457,f458,f40])).
% 2.49/0.69  fof(f40,plain,(
% 2.49/0.69    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f2])).
% 2.49/0.69  fof(f458,plain,(
% 2.49/0.69    ~r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),sK2)),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f79,f441,f29])).
% 2.49/0.69  fof(f29,plain,(
% 2.49/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f15])).
% 2.49/0.69  fof(f441,plain,(
% 2.49/0.69    ~r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),sK0)),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f437,f31])).
% 2.49/0.69  fof(f31,plain,(
% 2.49/0.69    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f15])).
% 2.49/0.69  fof(f79,plain,(
% 2.49/0.69    r1_tarski(sK2,sK0)),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f71,f45])).
% 2.49/0.69  fof(f45,plain,(
% 2.49/0.69    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 2.49/0.69    inference(equality_resolution,[],[f33])).
% 2.49/0.69  fof(f33,plain,(
% 2.49/0.69    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.49/0.69    inference(cnf_transformation,[],[f5])).
% 2.49/0.69  fof(f71,plain,(
% 2.49/0.69    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f22,f19,f27])).
% 2.49/0.69  fof(f27,plain,(
% 2.49/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f13])).
% 2.49/0.69  fof(f457,plain,(
% 2.49/0.69    ~r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),sK1)),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f87,f441,f29])).
% 2.49/0.69  fof(f87,plain,(
% 2.49/0.69    r1_tarski(sK1,sK0)),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f72,f45])).
% 2.49/0.69  fof(f72,plain,(
% 2.49/0.69    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.49/0.69    inference(unit_resulting_resolution,[],[f22,f21,f27])).
% 2.49/0.69  % SZS output end Proof for theBenchmark
% 2.49/0.69  % (31751)------------------------------
% 2.49/0.69  % (31751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.49/0.69  % (31751)Termination reason: Refutation
% 2.49/0.69  
% 2.49/0.69  % (31751)Memory used [KB]: 6908
% 2.49/0.69  % (31751)Time elapsed: 0.245 s
% 2.49/0.69  % (31751)------------------------------
% 2.49/0.69  % (31751)------------------------------
% 2.49/0.69  % (31726)Success in time 0.334 s
%------------------------------------------------------------------------------
