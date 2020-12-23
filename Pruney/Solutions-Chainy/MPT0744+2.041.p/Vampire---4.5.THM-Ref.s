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
% DateTime   : Thu Dec  3 12:55:35 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 396 expanded)
%              Number of leaves         :   11 (  87 expanded)
%              Depth                    :   20
%              Number of atoms          :  222 (1181 expanded)
%              Number of equality atoms :   22 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(subsumption_resolution,[],[f272,f61])).

fof(f61,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f272,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f258,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f258,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f257,f117])).

fof(f117,plain,(
    r1_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f116,f75])).

fof(f75,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f72,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(X0)
      | r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f72,plain,(
    v1_ordinal1(sK0) ),
    inference(resolution,[],[f28,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f28,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f116,plain,
    ( r2_hidden(sK0,sK0)
    | r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f103,f28])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(X0,sK0)
      | r1_tarski(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(X0,sK0)
      | r1_tarski(sK0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f71,f70])).

fof(f70,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(sK0,X1)
      | r1_tarski(sK0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f71,plain,(
    ! [X2] :
      ( r1_ordinal1(sK0,X2)
      | ~ v3_ordinal1(X2)
      | r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f28,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f257,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f222,f201])).

fof(f201,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f200,f154])).

fof(f154,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f151,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f151,plain,
    ( r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f150,f59])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f150,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f149,f27])).

fof(f27,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f149,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f144,f70])).

fof(f144,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f135,f57])).

fof(f57,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | r1_ordinal1(sK0,sK1) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f29,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f25,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k2_xboole_0(sK1,X0))
      | r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f133,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f133,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f132,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f132,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f98,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f68,f34])).

fof(f68,plain,(
    v1_ordinal1(sK1) ),
    inference(resolution,[],[f27,f31])).

fof(f98,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(subsumption_resolution,[],[f97,f27])).

fof(f97,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(resolution,[],[f69,f56])).

fof(f56,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f26,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X0] :
      ( r1_ordinal1(sK0,X0)
      | ~ r1_tarski(sK0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f200,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f199,f134])).

fof(f134,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f133,f108])).

fof(f108,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f96,f28])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(X0,sK1)
      | r1_tarski(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(X0,sK1)
      | r1_tarski(sK1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f67,f66])).

fof(f66,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(sK1,X1)
      | r1_tarski(sK1,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f27,f38])).

fof(f67,plain,(
    ! [X2] :
      ( r1_ordinal1(sK1,X2)
      | ~ v3_ordinal1(X2)
      | r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f27,f33])).

fof(f199,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f105,f28])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(sK1,X0)
      | sK1 = X0
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f74,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f74,plain,(
    ! [X1] :
      ( ~ r2_xboole_0(sK1,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(sK1,X1) ) ),
    inference(resolution,[],[f68,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f222,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(backward_demodulation,[],[f98,f201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:28:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (16155)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (16163)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (16164)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (16170)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (16152)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (16153)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (16151)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (16154)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (16150)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (16156)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (16176)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (16177)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (16167)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (16160)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (16158)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (16160)Refutation not found, incomplete strategy% (16160)------------------------------
% 0.22/0.55  % (16160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (16160)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (16160)Memory used [KB]: 10746
% 0.22/0.55  % (16160)Time elapsed: 0.138 s
% 0.22/0.55  % (16160)------------------------------
% 0.22/0.55  % (16160)------------------------------
% 0.22/0.56  % (16169)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (16166)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (16161)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (16174)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (16178)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.54/0.56  % (16161)Refutation not found, incomplete strategy% (16161)------------------------------
% 1.54/0.56  % (16161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (16161)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (16161)Memory used [KB]: 10746
% 1.54/0.56  % (16161)Time elapsed: 0.149 s
% 1.54/0.56  % (16161)------------------------------
% 1.54/0.56  % (16161)------------------------------
% 1.54/0.56  % (16171)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.54/0.56  % (16162)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.57  % (16172)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.54/0.57  % (16159)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.54/0.57  % (16171)Refutation found. Thanks to Tanya!
% 1.54/0.57  % SZS status Theorem for theBenchmark
% 1.54/0.57  % SZS output start Proof for theBenchmark
% 1.54/0.57  fof(f274,plain,(
% 1.54/0.57    $false),
% 1.54/0.57    inference(subsumption_resolution,[],[f272,f61])).
% 1.54/0.57  fof(f61,plain,(
% 1.54/0.57    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 1.54/0.57    inference(equality_resolution,[],[f60])).
% 1.54/0.57  fof(f60,plain,(
% 1.54/0.57    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 1.54/0.57    inference(equality_resolution,[],[f45])).
% 1.54/0.57  fof(f45,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.54/0.57    inference(cnf_transformation,[],[f4])).
% 1.54/0.57  fof(f4,axiom,(
% 1.54/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.54/0.57  fof(f272,plain,(
% 1.54/0.57    ~r2_hidden(sK0,k1_tarski(sK0))),
% 1.54/0.57    inference(resolution,[],[f258,f62])).
% 1.54/0.57  fof(f62,plain,(
% 1.54/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.54/0.57    inference(equality_resolution,[],[f55])).
% 1.54/0.57  fof(f55,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.54/0.57    inference(cnf_transformation,[],[f2])).
% 1.54/0.57  fof(f2,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.54/0.57  fof(f258,plain,(
% 1.54/0.57    ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 1.54/0.57    inference(subsumption_resolution,[],[f257,f117])).
% 1.54/0.57  fof(f117,plain,(
% 1.54/0.57    r1_tarski(sK0,sK0)),
% 1.54/0.57    inference(subsumption_resolution,[],[f116,f75])).
% 1.54/0.57  fof(f75,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(X0,sK0) | ~r2_hidden(X0,sK0)) )),
% 1.54/0.57    inference(resolution,[],[f72,f34])).
% 1.54/0.57  fof(f34,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v1_ordinal1(X0) | r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f20])).
% 1.54/0.57  fof(f20,plain,(
% 1.54/0.57    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f7])).
% 1.54/0.57  fof(f7,axiom,(
% 1.54/0.57    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 1.54/0.57  fof(f72,plain,(
% 1.54/0.57    v1_ordinal1(sK0)),
% 1.54/0.57    inference(resolution,[],[f28,f31])).
% 1.54/0.57  fof(f31,plain,(
% 1.54/0.57    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f17])).
% 1.54/0.57  fof(f17,plain,(
% 1.54/0.57    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f5])).
% 1.54/0.57  fof(f5,axiom,(
% 1.54/0.57    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 1.54/0.57  fof(f28,plain,(
% 1.54/0.57    v3_ordinal1(sK0)),
% 1.54/0.57    inference(cnf_transformation,[],[f14])).
% 1.54/0.57  fof(f14,plain,(
% 1.54/0.57    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f13])).
% 1.54/0.57  fof(f13,negated_conjecture,(
% 1.54/0.57    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.54/0.57    inference(negated_conjecture,[],[f12])).
% 1.54/0.57  fof(f12,conjecture,(
% 1.54/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.54/0.57  fof(f116,plain,(
% 1.54/0.57    r2_hidden(sK0,sK0) | r1_tarski(sK0,sK0)),
% 1.54/0.57    inference(resolution,[],[f103,f28])).
% 1.54/0.57  fof(f103,plain,(
% 1.54/0.57    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK0) | r1_tarski(sK0,X0)) )),
% 1.54/0.57    inference(duplicate_literal_removal,[],[f102])).
% 1.54/0.57  fof(f102,plain,(
% 1.54/0.57    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK0) | r1_tarski(sK0,X0) | ~v3_ordinal1(X0)) )),
% 1.54/0.57    inference(resolution,[],[f71,f70])).
% 1.54/0.57  fof(f70,plain,(
% 1.54/0.57    ( ! [X1] : (~r1_ordinal1(sK0,X1) | r1_tarski(sK0,X1) | ~v3_ordinal1(X1)) )),
% 1.54/0.57    inference(resolution,[],[f28,f38])).
% 1.54/0.57  fof(f38,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f22])).
% 1.54/0.57  fof(f22,plain,(
% 1.54/0.57    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.54/0.57    inference(flattening,[],[f21])).
% 1.54/0.57  fof(f21,plain,(
% 1.54/0.57    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f8])).
% 1.54/0.57  fof(f8,axiom,(
% 1.54/0.57    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.54/0.57  fof(f71,plain,(
% 1.54/0.57    ( ! [X2] : (r1_ordinal1(sK0,X2) | ~v3_ordinal1(X2) | r2_hidden(X2,sK0)) )),
% 1.54/0.57    inference(resolution,[],[f28,f33])).
% 1.54/0.57  fof(f33,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f19])).
% 1.54/0.57  fof(f19,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.54/0.57    inference(flattening,[],[f18])).
% 1.54/0.57  fof(f18,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f10])).
% 1.54/0.57  fof(f10,axiom,(
% 1.54/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.54/0.57  fof(f257,plain,(
% 1.54/0.57    ~r1_tarski(sK0,sK0) | ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 1.54/0.57    inference(forward_demodulation,[],[f222,f201])).
% 1.54/0.57  fof(f201,plain,(
% 1.54/0.57    sK0 = sK1),
% 1.54/0.57    inference(subsumption_resolution,[],[f200,f154])).
% 1.54/0.57  fof(f154,plain,(
% 1.54/0.57    ~r2_hidden(sK1,sK0) | sK0 = sK1),
% 1.54/0.57    inference(resolution,[],[f151,f49])).
% 1.54/0.57  fof(f49,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f24])).
% 1.54/0.57  fof(f24,plain,(
% 1.54/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.54/0.57    inference(ennf_transformation,[],[f11])).
% 1.54/0.57  fof(f11,axiom,(
% 1.54/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.54/0.57  fof(f151,plain,(
% 1.54/0.57    r1_tarski(sK0,sK1) | sK0 = sK1),
% 1.54/0.57    inference(resolution,[],[f150,f59])).
% 1.54/0.57  fof(f59,plain,(
% 1.54/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.54/0.57    inference(equality_resolution,[],[f46])).
% 1.54/0.57  fof(f46,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.54/0.57    inference(cnf_transformation,[],[f4])).
% 1.54/0.57  fof(f150,plain,(
% 1.54/0.57    r2_hidden(sK0,k1_tarski(sK1)) | r1_tarski(sK0,sK1)),
% 1.54/0.57    inference(subsumption_resolution,[],[f149,f27])).
% 1.54/0.57  fof(f27,plain,(
% 1.54/0.57    v3_ordinal1(sK1)),
% 1.54/0.57    inference(cnf_transformation,[],[f14])).
% 1.54/0.57  fof(f149,plain,(
% 1.54/0.57    r2_hidden(sK0,k1_tarski(sK1)) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1)),
% 1.54/0.57    inference(resolution,[],[f144,f70])).
% 1.54/0.57  fof(f144,plain,(
% 1.54/0.57    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_tarski(sK1))),
% 1.54/0.57    inference(resolution,[],[f135,f57])).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | r1_ordinal1(sK0,sK1)),
% 1.54/0.57    inference(definition_unfolding,[],[f25,f29])).
% 1.54/0.57  fof(f29,plain,(
% 1.54/0.57    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f6])).
% 1.54/0.57  fof(f6,axiom,(
% 1.54/0.57    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.54/0.57  fof(f25,plain,(
% 1.54/0.57    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.54/0.57    inference(cnf_transformation,[],[f14])).
% 1.54/0.57  fof(f135,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(sK0,k2_xboole_0(sK1,X0)) | r2_hidden(sK0,X0)) )),
% 1.54/0.57    inference(resolution,[],[f133,f64])).
% 1.54/0.57  fof(f64,plain,(
% 1.54/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.54/0.57    inference(equality_resolution,[],[f53])).
% 1.54/0.57  fof(f53,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.54/0.57    inference(cnf_transformation,[],[f2])).
% 1.54/0.57  fof(f133,plain,(
% 1.54/0.57    ~r2_hidden(sK0,sK1)),
% 1.54/0.57    inference(subsumption_resolution,[],[f132,f63])).
% 1.54/0.57  fof(f63,plain,(
% 1.54/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 1.54/0.57    inference(equality_resolution,[],[f54])).
% 1.54/0.57  fof(f54,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.54/0.57    inference(cnf_transformation,[],[f2])).
% 1.54/0.57  fof(f132,plain,(
% 1.54/0.57    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~r2_hidden(sK0,sK1)),
% 1.54/0.57    inference(resolution,[],[f98,f73])).
% 1.54/0.57  fof(f73,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(X0,sK1) | ~r2_hidden(X0,sK1)) )),
% 1.54/0.57    inference(resolution,[],[f68,f34])).
% 1.54/0.57  fof(f68,plain,(
% 1.54/0.57    v1_ordinal1(sK1)),
% 1.54/0.57    inference(resolution,[],[f27,f31])).
% 1.54/0.57  fof(f98,plain,(
% 1.54/0.57    ~r1_tarski(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.54/0.57    inference(subsumption_resolution,[],[f97,f27])).
% 1.54/0.57  fof(f97,plain,(
% 1.54/0.57    ~r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.54/0.57    inference(resolution,[],[f69,f56])).
% 1.54/0.57  fof(f56,plain,(
% 1.54/0.57    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.54/0.57    inference(definition_unfolding,[],[f26,f29])).
% 1.54/0.57  fof(f26,plain,(
% 1.54/0.57    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.54/0.57    inference(cnf_transformation,[],[f14])).
% 1.54/0.57  fof(f69,plain,(
% 1.54/0.57    ( ! [X0] : (r1_ordinal1(sK0,X0) | ~r1_tarski(sK0,X0) | ~v3_ordinal1(X0)) )),
% 1.54/0.57    inference(resolution,[],[f28,f37])).
% 1.54/0.57  fof(f37,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | r1_ordinal1(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f22])).
% 1.54/0.57  fof(f200,plain,(
% 1.54/0.57    r2_hidden(sK1,sK0) | sK0 = sK1),
% 1.54/0.57    inference(subsumption_resolution,[],[f199,f134])).
% 1.54/0.57  fof(f134,plain,(
% 1.54/0.57    r1_tarski(sK1,sK0)),
% 1.54/0.57    inference(resolution,[],[f133,f108])).
% 1.54/0.57  fof(f108,plain,(
% 1.54/0.57    r2_hidden(sK0,sK1) | r1_tarski(sK1,sK0)),
% 1.54/0.57    inference(resolution,[],[f96,f28])).
% 1.54/0.57  fof(f96,plain,(
% 1.54/0.57    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK1) | r1_tarski(sK1,X0)) )),
% 1.54/0.57    inference(duplicate_literal_removal,[],[f95])).
% 1.54/0.57  fof(f95,plain,(
% 1.54/0.57    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK1) | r1_tarski(sK1,X0) | ~v3_ordinal1(X0)) )),
% 1.54/0.57    inference(resolution,[],[f67,f66])).
% 1.54/0.57  fof(f66,plain,(
% 1.54/0.57    ( ! [X1] : (~r1_ordinal1(sK1,X1) | r1_tarski(sK1,X1) | ~v3_ordinal1(X1)) )),
% 1.54/0.57    inference(resolution,[],[f27,f38])).
% 1.54/0.57  fof(f67,plain,(
% 1.54/0.57    ( ! [X2] : (r1_ordinal1(sK1,X2) | ~v3_ordinal1(X2) | r2_hidden(X2,sK1)) )),
% 1.54/0.57    inference(resolution,[],[f27,f33])).
% 1.54/0.57  fof(f199,plain,(
% 1.54/0.57    r2_hidden(sK1,sK0) | sK0 = sK1 | ~r1_tarski(sK1,sK0)),
% 1.54/0.57    inference(resolution,[],[f105,f28])).
% 1.54/0.57  fof(f105,plain,(
% 1.54/0.57    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK1,X0) | sK1 = X0 | ~r1_tarski(sK1,X0)) )),
% 1.54/0.57    inference(resolution,[],[f74,f41])).
% 1.54/0.57  fof(f41,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f3])).
% 1.54/0.57  fof(f3,axiom,(
% 1.54/0.57    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.54/0.57  fof(f74,plain,(
% 1.54/0.57    ( ! [X1] : (~r2_xboole_0(sK1,X1) | ~v3_ordinal1(X1) | r2_hidden(sK1,X1)) )),
% 1.54/0.57    inference(resolution,[],[f68,f30])).
% 1.54/0.57  fof(f30,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v1_ordinal1(X0) | ~v3_ordinal1(X1) | ~r2_xboole_0(X0,X1) | r2_hidden(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f16])).
% 1.54/0.57  fof(f16,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.54/0.57    inference(flattening,[],[f15])).
% 1.54/0.57  fof(f15,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f9])).
% 1.54/0.57  fof(f9,axiom,(
% 1.54/0.57    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).
% 1.54/0.57  fof(f222,plain,(
% 1.54/0.57    ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) | ~r1_tarski(sK0,sK1)),
% 1.54/0.57    inference(backward_demodulation,[],[f98,f201])).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (16171)------------------------------
% 1.54/0.57  % (16171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (16171)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (16171)Memory used [KB]: 1791
% 1.54/0.57  % (16171)Time elapsed: 0.150 s
% 1.54/0.57  % (16171)------------------------------
% 1.54/0.57  % (16171)------------------------------
% 1.54/0.57  % (16149)Success in time 0.201 s
%------------------------------------------------------------------------------
