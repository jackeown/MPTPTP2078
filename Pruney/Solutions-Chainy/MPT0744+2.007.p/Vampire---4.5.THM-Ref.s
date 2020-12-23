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
% DateTime   : Thu Dec  3 12:55:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 358 expanded)
%              Number of leaves         :   14 (  84 expanded)
%              Depth                    :   21
%              Number of atoms          :  216 ( 965 expanded)
%              Number of equality atoms :   25 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f273,plain,(
    $false ),
    inference(subsumption_resolution,[],[f272,f131])).

fof(f131,plain,(
    ~ r2_hidden(sK0,sK0) ),
    inference(resolution,[],[f129,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f129,plain,(
    r1_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f128,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f128,plain,
    ( r1_tarski(sK0,sK0)
    | r2_hidden(sK0,sK0) ),
    inference(resolution,[],[f126,f34])).

fof(f34,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f126,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r1_tarski(X1,sK0)
      | r2_hidden(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f124,f34])).

fof(f124,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(sK0)
      | r2_hidden(sK0,X1) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(sK0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(sK0,X1) ) ),
    inference(resolution,[],[f99,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f99,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(X1,sK0)
      | r1_tarski(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f45,f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f272,plain,(
    r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f271,f196])).

fof(f196,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f190,f178])).

fof(f178,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f177,f42])).

fof(f177,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f174,f47])).

fof(f174,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f173,f101])).

fof(f101,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f98,f34])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(X0,sK1)
      | ~ r1_ordinal1(X0,sK1) ) ),
    inference(resolution,[],[f45,f33])).

fof(f33,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f173,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK0,sK1)
    | r1_ordinal1(sK0,sK1) ),
    inference(forward_demodulation,[],[f171,f58])).

fof(f58,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f171,plain,
    ( r2_hidden(sK0,sK1)
    | r1_ordinal1(sK0,sK1)
    | r1_tarski(sK0,k3_tarski(k2_tarski(sK1,sK1))) ),
    inference(resolution,[],[f107,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f107,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK1))
    | r2_hidden(sK0,sK1)
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f61,f56])).

fof(f56,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | r1_ordinal1(sK0,sK1) ),
    inference(definition_unfolding,[],[f31,f54])).

fof(f54,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f38,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f31,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
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

fof(f190,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f184,f92])).

fof(f92,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f91,f34])).

fof(f91,plain,
    ( ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f90,f33])).

fof(f90,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(definition_unfolding,[],[f32,f54])).

fof(f32,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f184,plain,(
    ! [X0] :
      ( r2_hidden(sK0,k2_xboole_0(sK1,X0))
      | sK0 = sK1 ) ),
    inference(resolution,[],[f183,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f183,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f182,f34])).

fof(f182,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f181,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f181,plain,
    ( ~ v1_ordinal1(sK0)
    | r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f180,f33])).

fof(f180,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK0)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f176,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f176,plain,
    ( r2_xboole_0(sK0,sK1)
    | sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f174,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f271,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f214,f57])).

fof(f57,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f35,f54])).

fof(f35,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f214,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f92,f196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (1250)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (1268)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (1244)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (1259)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (1246)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (1250)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f273,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f272,f131])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK0)),
% 0.20/0.51    inference(resolution,[],[f129,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    r1_tarski(sK0,sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f128,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    r1_tarski(sK0,sK0) | r2_hidden(sK0,sK0)),
% 0.20/0.51    inference(resolution,[],[f126,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    v3_ordinal1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f14])).
% 0.20/0.51  fof(f14,conjecture,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ( ! [X1] : (~v3_ordinal1(X1) | r1_tarski(X1,sK0) | r2_hidden(sK0,X1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f124,f34])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,sK0) | ~v3_ordinal1(X1) | ~v3_ordinal1(sK0) | r2_hidden(sK0,X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,sK0) | ~v3_ordinal1(X1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(X1) | r2_hidden(sK0,X1)) )),
% 0.20/0.51    inference(resolution,[],[f99,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ( ! [X1] : (~r1_ordinal1(X1,sK0) | r1_tarski(X1,sK0) | ~v3_ordinal1(X1)) )),
% 0.20/0.51    inference(resolution,[],[f45,f34])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.51  fof(f272,plain,(
% 0.20/0.51    r2_hidden(sK0,sK0)),
% 0.20/0.51    inference(forward_demodulation,[],[f271,f196])).
% 0.20/0.51  fof(f196,plain,(
% 0.20/0.51    sK0 = sK1),
% 0.20/0.51    inference(subsumption_resolution,[],[f190,f178])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    ~r2_hidden(sK1,sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f177,f42])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 0.20/0.51    inference(resolution,[],[f174,f47])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f173,f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ~r1_ordinal1(sK0,sK1) | r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f98,f34])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(X0,sK1) | ~r1_ordinal1(X0,sK1)) )),
% 0.20/0.51    inference(resolution,[],[f45,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    v3_ordinal1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | r2_hidden(sK0,sK1) | r1_ordinal1(sK0,sK1)),
% 0.20/0.51    inference(forward_demodulation,[],[f171,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f36,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    r2_hidden(sK0,sK1) | r1_ordinal1(sK0,sK1) | r1_tarski(sK0,k3_tarski(k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(resolution,[],[f107,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    r2_hidden(sK0,k2_tarski(sK1,sK1)) | r2_hidden(sK0,sK1) | r1_ordinal1(sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f61,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | r1_ordinal1(sK0,sK1)),
% 0.20/0.51    inference(definition_unfolding,[],[f31,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f38,f37])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    sK0 = sK1 | r2_hidden(sK1,sK0)),
% 0.20/0.51    inference(resolution,[],[f184,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | r2_hidden(sK1,sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f91,f34])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f90,f33])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(resolution,[],[f41,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(definition_unfolding,[],[f32,f54])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK0,k2_xboole_0(sK1,X0)) | sK0 = sK1) )),
% 0.20/0.51    inference(resolution,[],[f183,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(equality_resolution,[],[f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.20/0.51    inference(subsumption_resolution,[],[f182,f34])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.20/0.51    inference(resolution,[],[f181,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    ~v1_ordinal1(sK0) | r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.20/0.51    inference(subsumption_resolution,[],[f180,f33])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    sK0 = sK1 | r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v1_ordinal1(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f179])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    sK0 = sK1 | r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v1_ordinal1(sK0) | r2_hidden(sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f176,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    r2_xboole_0(sK0,sK1) | sK0 = sK1 | r2_hidden(sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f174,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.20/0.51    inference(unused_predicate_definition_removal,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.51  fof(f271,plain,(
% 0.20/0.51    r2_hidden(sK1,sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f214,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f35,f54])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | r2_hidden(sK1,sK0)),
% 0.20/0.51    inference(backward_demodulation,[],[f92,f196])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (1250)------------------------------
% 0.20/0.51  % (1250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1250)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (1250)Memory used [KB]: 6396
% 0.20/0.51  % (1250)Time elapsed: 0.106 s
% 0.20/0.51  % (1250)------------------------------
% 0.20/0.51  % (1250)------------------------------
% 0.20/0.51  % (1261)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (1240)Success in time 0.151 s
%------------------------------------------------------------------------------
