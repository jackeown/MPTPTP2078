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
% DateTime   : Thu Dec  3 12:51:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 667 expanded)
%              Number of leaves         :    8 ( 198 expanded)
%              Depth                    :   22
%              Number of atoms          :  118 (1287 expanded)
%              Number of equality atoms :   28 ( 288 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f606,plain,(
    $false ),
    inference(resolution,[],[f599,f59])).

fof(f59,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f49,f51])).

% (31221)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f45,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f24,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f599,plain,(
    r2_hidden(sK7(sK1,sK0),o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f594,f576])).

fof(f576,plain,(
    o_0_0_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f575,f47])).

fof(f47,plain,
    ( o_0_0_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f22,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f575,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f572,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f572,plain,(
    sP6(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f571])).

fof(f571,plain,
    ( sP6(sK0,sK1)
    | sP6(sK0,sK1) ),
    inference(resolution,[],[f570,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f570,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | sP6(sK0,sK1) ),
    inference(global_subsumption,[],[f23,f568])).

fof(f568,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | sP6(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f567])).

fof(f567,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | sP6(sK0,sK1) ),
    inference(superposition,[],[f48,f526])).

fof(f526,plain,(
    ! [X6,X5] :
      ( o_0_0_xboole_0 = k11_relat_1(X5,X6)
      | ~ v1_relat_1(X5)
      | sP6(X6,X5) ) ),
    inference(resolution,[],[f384,f34])).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f384,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,sK5(o_0_0_xboole_0,k11_relat_1(X0,X1))),X0)
      | ~ v1_relat_1(X0)
      | o_0_0_xboole_0 = k11_relat_1(X0,X1) ) ),
    inference(resolution,[],[f359,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f359,plain,(
    ! [X0] :
      ( r2_hidden(sK5(o_0_0_xboole_0,X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f208,f311])).

fof(f311,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f272,f310])).

fof(f310,plain,(
    o_0_0_xboole_0 = k1_relat_1(k1_relat_1(o_0_0_xboole_0)) ),
    inference(forward_demodulation,[],[f203,f256])).

fof(f256,plain,(
    k1_relat_1(o_0_0_xboole_0) = k10_relat_1(sK1,o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f207,f205])).

fof(f205,plain,(
    k1_relat_1(o_0_0_xboole_0) = k1_relat_1(k10_relat_1(sK1,o_0_0_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f69,f159,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sP6(sK5(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f159,plain,(
    ! [X0] : ~ sP6(X0,k10_relat_1(sK1,o_0_0_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f131,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0)
      | ~ sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f131,plain,(
    ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,o_0_0_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f23,f59,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f69,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(o_0_0_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f63,f52])).

fof(f63,plain,(
    ! [X0] : ~ sP6(X0,o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f59,f33])).

fof(f207,plain,(
    k10_relat_1(sK1,o_0_0_xboole_0) = k1_relat_1(k10_relat_1(sK1,o_0_0_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f131,f159,f37])).

fof(f203,plain,(
    o_0_0_xboole_0 = k1_relat_1(k10_relat_1(sK1,o_0_0_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f59,f159,f37])).

fof(f272,plain,(
    k1_relat_1(o_0_0_xboole_0) = k1_relat_1(k1_relat_1(o_0_0_xboole_0)) ),
    inference(backward_demodulation,[],[f205,f256])).

fof(f208,plain,(
    ! [X0] :
      ( r2_hidden(sK5(o_0_0_xboole_0,X0),X0)
      | k1_relat_1(o_0_0_xboole_0) = X0 ) ),
    inference(resolution,[],[f37,f63])).

fof(f48,plain,
    ( o_0_0_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f21,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f594,plain,(
    r2_hidden(sK7(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f23,f574,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f574,plain,(
    r2_hidden(k4_tarski(sK0,sK7(sK1,sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f572,f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (31193)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (31201)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (31198)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (31216)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (31217)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (31208)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (31199)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (31209)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (31214)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (31218)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (31200)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (31194)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (31197)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (31206)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (31217)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f606,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(resolution,[],[f599,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0)) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f49,f51])).
% 0.21/0.53  % (31221)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f45,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (r1_xboole_0(X0,o_0_0_xboole_0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.53  fof(f599,plain,(
% 0.21/0.53    r2_hidden(sK7(sK1,sK0),o_0_0_xboole_0)),
% 0.21/0.53    inference(forward_demodulation,[],[f594,f576])).
% 0.21/0.53  fof(f576,plain,(
% 0.21/0.53    o_0_0_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f575,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    o_0_0_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f24])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.53  fof(f575,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f572,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0] : (r2_hidden(X2,k1_relat_1(X0)) | ~sP6(X2,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP6(X2,X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.53  fof(f572,plain,(
% 0.21/0.53    sP6(sK0,sK1)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f571])).
% 0.21/0.53  fof(f571,plain,(
% 0.21/0.53    sP6(sK0,sK1) | sP6(sK0,sK1)),
% 0.21/0.53    inference(resolution,[],[f570,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | sP6(X2,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP6(X2,X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f570,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_relat_1(sK1)) | sP6(sK0,sK1)),
% 0.21/0.53    inference(global_subsumption,[],[f23,f568])).
% 0.21/0.53  fof(f568,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | sP6(sK0,sK1)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f567])).
% 0.21/0.53  fof(f567,plain,(
% 0.21/0.53    o_0_0_xboole_0 != o_0_0_xboole_0 | r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | sP6(sK0,sK1)),
% 0.21/0.53    inference(superposition,[],[f48,f526])).
% 0.21/0.53  fof(f526,plain,(
% 0.21/0.53    ( ! [X6,X5] : (o_0_0_xboole_0 = k11_relat_1(X5,X6) | ~v1_relat_1(X5) | sP6(X6,X5)) )),
% 0.21/0.53    inference(resolution,[],[f384,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | sP6(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f384,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,sK5(o_0_0_xboole_0,k11_relat_1(X0,X1))),X0) | ~v1_relat_1(X0) | o_0_0_xboole_0 = k11_relat_1(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f359,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.53  fof(f359,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK5(o_0_0_xboole_0,X0),X0) | o_0_0_xboole_0 = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f208,f311])).
% 0.21/0.53  fof(f311,plain,(
% 0.21/0.53    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 0.21/0.53    inference(backward_demodulation,[],[f272,f310])).
% 0.21/0.53  fof(f310,plain,(
% 0.21/0.53    o_0_0_xboole_0 = k1_relat_1(k1_relat_1(o_0_0_xboole_0))),
% 0.21/0.53    inference(forward_demodulation,[],[f203,f256])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    k1_relat_1(o_0_0_xboole_0) = k10_relat_1(sK1,o_0_0_xboole_0)),
% 0.21/0.53    inference(backward_demodulation,[],[f207,f205])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    k1_relat_1(o_0_0_xboole_0) = k1_relat_1(k10_relat_1(sK1,o_0_0_xboole_0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f69,f159,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP6(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    ( ! [X0] : (~sP6(X0,k10_relat_1(sK1,o_0_0_xboole_0))) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f131,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0) | ~sP6(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,o_0_0_xboole_0))) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f23,f59,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(o_0_0_xboole_0))) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f63,f52])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0] : (~sP6(X0,o_0_0_xboole_0)) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f59,f33])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    k10_relat_1(sK1,o_0_0_xboole_0) = k1_relat_1(k10_relat_1(sK1,o_0_0_xboole_0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f131,f159,f37])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    o_0_0_xboole_0 = k1_relat_1(k10_relat_1(sK1,o_0_0_xboole_0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f59,f159,f37])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    k1_relat_1(o_0_0_xboole_0) = k1_relat_1(k1_relat_1(o_0_0_xboole_0))),
% 0.21/0.53    inference(backward_demodulation,[],[f205,f256])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK5(o_0_0_xboole_0,X0),X0) | k1_relat_1(o_0_0_xboole_0) = X0) )),
% 0.21/0.53    inference(resolution,[],[f37,f63])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    o_0_0_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.53    inference(definition_unfolding,[],[f21,f24])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    v1_relat_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f594,plain,(
% 0.21/0.53    r2_hidden(sK7(sK1,sK0),k11_relat_1(sK1,sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f23,f574,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f574,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK7(sK1,sK0)),sK1)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f572,f33])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (31217)------------------------------
% 0.21/0.53  % (31217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31217)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (31217)Memory used [KB]: 6652
% 0.21/0.53  % (31217)Time elapsed: 0.114 s
% 0.21/0.53  % (31217)------------------------------
% 0.21/0.53  % (31217)------------------------------
% 0.21/0.53  % (31205)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31195)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (31213)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (31192)Success in time 0.177 s
%------------------------------------------------------------------------------
