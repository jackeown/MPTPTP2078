%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 451 expanded)
%              Number of leaves         :   12 ( 126 expanded)
%              Depth                    :   21
%              Number of atoms          :  157 ( 900 expanded)
%              Number of equality atoms :   49 ( 377 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1036,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1035,f59])).

fof(f59,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f20,f22])).

fof(f22,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f20,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f1035,plain,(
    sK0 = k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f1034,f734])).

fof(f734,plain,(
    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(subsumption_resolution,[],[f733,f640])).

fof(f640,plain,(
    ! [X8] :
      ( r2_hidden(sK4(X8,sK1,X8),sK0)
      | k3_tarski(k1_enumset1(X8,X8,sK1)) = X8 ) ),
    inference(forward_demodulation,[],[f639,f495])).

fof(f495,plain,(
    sK1 = k4_subset_1(sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f197,f493])).

fof(f493,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(subsumption_resolution,[],[f492,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f492,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0
      | ~ r2_hidden(sK4(X0,X0,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f474])).

fof(f474,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0
      | ~ r2_hidden(sK4(X0,X0,X0),X0)
      | k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ) ),
    inference(resolution,[],[f399,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f399,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X3)
      | k3_tarski(k1_enumset1(X2,X2,X3)) = X2 ) ),
    inference(subsumption_resolution,[],[f392,f53])).

fof(f392,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X2)
      | r2_hidden(sK4(X2,X3,X2),X3)
      | k3_tarski(k1_enumset1(X2,X2,X3)) = X2 ) ),
    inference(factoring,[],[f51])).

fof(f197,plain,(
    k4_subset_1(sK0,sK1,sK1) = k3_tarski(k1_enumset1(sK1,sK1,sK1)) ),
    inference(resolution,[],[f131,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k3_tarski(k1_enumset1(X0,X0,sK1)) ) ),
    inference(resolution,[],[f47,f19])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f639,plain,(
    ! [X8] :
      ( k3_tarski(k1_enumset1(X8,X8,sK1)) = X8
      | r2_hidden(sK4(X8,k4_subset_1(sK0,sK1,sK1),X8),sK0) ) ),
    inference(forward_demodulation,[],[f479,f495])).

fof(f479,plain,(
    ! [X8] :
      ( k3_tarski(k1_enumset1(X8,X8,k4_subset_1(sK0,sK1,sK1))) = X8
      | r2_hidden(sK4(X8,k4_subset_1(sK0,sK1,sK1),X8),sK0) ) ),
    inference(resolution,[],[f399,f453])).

fof(f453,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_subset_1(sK0,sK1,sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f451,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
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

fof(f451,plain,(
    r1_tarski(k4_subset_1(sK0,sK1,sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f448])).

fof(f448,plain,
    ( r1_tarski(k4_subset_1(sK0,sK1,sK1),sK0)
    | r1_tarski(k4_subset_1(sK0,sK1,sK1),sK0) ),
    inference(resolution,[],[f300,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f300,plain,(
    ! [X7] :
      ( r2_hidden(sK2(k4_subset_1(sK0,sK1,sK1),X7),sK0)
      | r1_tarski(k4_subset_1(sK0,sK1,sK1),X7) ) ),
    inference(resolution,[],[f219,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f31,f67])).

fof(f67,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f65,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f65,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f61,f21])).

fof(f21,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f61,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f30,f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

% (21945)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f219,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k4_subset_1(sK0,sK1,sK1),X1),sK1)
      | r1_tarski(k4_subset_1(sK0,sK1,sK1),X1) ) ),
    inference(resolution,[],[f209,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f209,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_subset_1(sK0,sK1,sK1))
      | r2_hidden(X2,sK1) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_subset_1(sK0,sK1,sK1))
      | r2_hidden(X2,sK1)
      | r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f58,f197])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_tarski(k1_enumset1(X0,X0,X1)))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f733,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ r2_hidden(sK4(sK0,sK1,sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f730])).

fof(f730,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ r2_hidden(sK4(sK0,sK1,sK0),sK0)
    | sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(resolution,[],[f640,f53])).

fof(f1034,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f1031,f46])).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f24,f26,f26])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1031,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK0)) ),
    inference(resolution,[],[f132,f19])).

fof(f132,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X2,X1,X2) ) ),
    inference(resolution,[],[f47,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f23,f22])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (21898)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (21905)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.45  % (21905)Refutation not found, incomplete strategy% (21905)------------------------------
% 0.21/0.45  % (21905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (21905)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (21905)Memory used [KB]: 10618
% 0.21/0.45  % (21905)Time elapsed: 0.055 s
% 0.21/0.45  % (21905)------------------------------
% 0.21/0.45  % (21905)------------------------------
% 0.21/0.46  % (21915)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (21908)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (21900)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (21916)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (21916)Refutation not found, incomplete strategy% (21916)------------------------------
% 0.21/0.52  % (21916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21916)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21916)Memory used [KB]: 10746
% 0.21/0.52  % (21916)Time elapsed: 0.073 s
% 0.21/0.52  % (21916)------------------------------
% 0.21/0.52  % (21916)------------------------------
% 0.21/0.53  % (21895)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (21897)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (21906)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (21923)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (21894)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (21896)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (21913)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (21920)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (21910)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (21921)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (21922)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (21909)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (21899)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (21912)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (21919)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (21918)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (21911)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (21907)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (21904)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (21902)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (21917)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (21901)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (21903)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (21914)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (21904)Refutation not found, incomplete strategy% (21904)------------------------------
% 0.21/0.56  % (21904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21904)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21904)Memory used [KB]: 10618
% 0.21/0.56  % (21904)Time elapsed: 0.157 s
% 0.21/0.56  % (21904)------------------------------
% 0.21/0.56  % (21904)------------------------------
% 0.21/0.57  % (21911)Refutation not found, incomplete strategy% (21911)------------------------------
% 0.21/0.57  % (21911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21911)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (21911)Memory used [KB]: 10618
% 0.21/0.57  % (21911)Time elapsed: 0.151 s
% 0.21/0.57  % (21911)------------------------------
% 0.21/0.57  % (21911)------------------------------
% 0.21/0.59  % (21900)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 1.84/0.60  % SZS output start Proof for theBenchmark
% 1.84/0.60  fof(f1036,plain,(
% 1.84/0.60    $false),
% 1.84/0.60    inference(subsumption_resolution,[],[f1035,f59])).
% 1.84/0.60  fof(f59,plain,(
% 1.84/0.60    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 1.84/0.60    inference(backward_demodulation,[],[f20,f22])).
% 1.84/0.60  fof(f22,plain,(
% 1.84/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.84/0.60    inference(cnf_transformation,[],[f8])).
% 1.84/0.60  fof(f8,axiom,(
% 1.84/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.84/0.60  fof(f20,plain,(
% 1.84/0.60    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.84/0.60    inference(cnf_transformation,[],[f14])).
% 1.84/0.60  fof(f14,plain,(
% 1.84/0.60    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.84/0.60    inference(ennf_transformation,[],[f13])).
% 1.84/0.60  fof(f13,negated_conjecture,(
% 1.84/0.60    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.84/0.60    inference(negated_conjecture,[],[f12])).
% 1.84/0.60  fof(f12,conjecture,(
% 1.84/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 1.84/0.60  fof(f1035,plain,(
% 1.84/0.60    sK0 = k4_subset_1(sK0,sK1,sK0)),
% 1.84/0.60    inference(forward_demodulation,[],[f1034,f734])).
% 1.84/0.60  fof(f734,plain,(
% 1.84/0.60    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.84/0.60    inference(subsumption_resolution,[],[f733,f640])).
% 1.84/0.60  fof(f640,plain,(
% 1.84/0.60    ( ! [X8] : (r2_hidden(sK4(X8,sK1,X8),sK0) | k3_tarski(k1_enumset1(X8,X8,sK1)) = X8) )),
% 1.84/0.60    inference(forward_demodulation,[],[f639,f495])).
% 1.84/0.60  fof(f495,plain,(
% 1.84/0.60    sK1 = k4_subset_1(sK0,sK1,sK1)),
% 1.84/0.60    inference(backward_demodulation,[],[f197,f493])).
% 1.84/0.60  fof(f493,plain,(
% 1.84/0.60    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f492,f51])).
% 1.84/0.60  fof(f51,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k3_tarski(k1_enumset1(X0,X0,X1)) = X2) )),
% 1.84/0.60    inference(definition_unfolding,[],[f41,f45])).
% 1.84/0.60  fof(f45,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.84/0.60    inference(definition_unfolding,[],[f25,f26])).
% 1.84/0.60  fof(f26,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f4])).
% 1.84/0.60  fof(f4,axiom,(
% 1.84/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.84/0.60  fof(f25,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.84/0.60    inference(cnf_transformation,[],[f6])).
% 1.84/0.60  fof(f6,axiom,(
% 1.84/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.84/0.60  fof(f41,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 1.84/0.60    inference(cnf_transformation,[],[f2])).
% 1.84/0.60  fof(f2,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.84/0.60  fof(f492,plain,(
% 1.84/0.60    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0 | ~r2_hidden(sK4(X0,X0,X0),X0)) )),
% 1.84/0.60    inference(duplicate_literal_removal,[],[f474])).
% 1.84/0.60  fof(f474,plain,(
% 1.84/0.60    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0 | ~r2_hidden(sK4(X0,X0,X0),X0) | k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 1.84/0.60    inference(resolution,[],[f399,f53])).
% 1.84/0.60  fof(f53,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | k3_tarski(k1_enumset1(X0,X0,X1)) = X2) )),
% 1.84/0.60    inference(definition_unfolding,[],[f39,f45])).
% 1.84/0.60  fof(f39,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 1.84/0.60    inference(cnf_transformation,[],[f2])).
% 1.84/0.60  fof(f399,plain,(
% 1.84/0.60    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X3) | k3_tarski(k1_enumset1(X2,X2,X3)) = X2) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f392,f53])).
% 1.84/0.60  fof(f392,plain,(
% 1.84/0.60    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X2) | r2_hidden(sK4(X2,X3,X2),X3) | k3_tarski(k1_enumset1(X2,X2,X3)) = X2) )),
% 1.84/0.60    inference(factoring,[],[f51])).
% 1.84/0.60  fof(f197,plain,(
% 1.84/0.60    k4_subset_1(sK0,sK1,sK1) = k3_tarski(k1_enumset1(sK1,sK1,sK1))),
% 1.84/0.60    inference(resolution,[],[f131,f19])).
% 1.84/0.60  fof(f19,plain,(
% 1.84/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.84/0.60    inference(cnf_transformation,[],[f14])).
% 1.84/0.60  fof(f131,plain,(
% 1.84/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k3_tarski(k1_enumset1(X0,X0,sK1))) )),
% 1.84/0.60    inference(resolution,[],[f47,f19])).
% 1.84/0.60  fof(f47,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 1.84/0.60    inference(definition_unfolding,[],[f38,f45])).
% 1.84/0.60  fof(f38,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f18])).
% 1.84/0.60  fof(f18,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.84/0.60    inference(flattening,[],[f17])).
% 1.84/0.60  fof(f17,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.84/0.60    inference(ennf_transformation,[],[f11])).
% 1.84/0.60  fof(f11,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.84/0.60  fof(f639,plain,(
% 1.84/0.60    ( ! [X8] : (k3_tarski(k1_enumset1(X8,X8,sK1)) = X8 | r2_hidden(sK4(X8,k4_subset_1(sK0,sK1,sK1),X8),sK0)) )),
% 1.84/0.60    inference(forward_demodulation,[],[f479,f495])).
% 1.84/0.60  fof(f479,plain,(
% 1.84/0.60    ( ! [X8] : (k3_tarski(k1_enumset1(X8,X8,k4_subset_1(sK0,sK1,sK1))) = X8 | r2_hidden(sK4(X8,k4_subset_1(sK0,sK1,sK1),X8),sK0)) )),
% 1.84/0.60    inference(resolution,[],[f399,f453])).
% 1.84/0.60  fof(f453,plain,(
% 1.84/0.60    ( ! [X0] : (~r2_hidden(X0,k4_subset_1(sK0,sK1,sK1)) | r2_hidden(X0,sK0)) )),
% 1.84/0.60    inference(resolution,[],[f451,f31])).
% 1.84/0.60  fof(f31,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f16])).
% 1.84/0.60  fof(f16,plain,(
% 1.84/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.84/0.60    inference(ennf_transformation,[],[f1])).
% 1.84/0.60  fof(f1,axiom,(
% 1.84/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.84/0.60  fof(f451,plain,(
% 1.84/0.60    r1_tarski(k4_subset_1(sK0,sK1,sK1),sK0)),
% 1.84/0.60    inference(duplicate_literal_removal,[],[f448])).
% 1.84/0.60  fof(f448,plain,(
% 1.84/0.60    r1_tarski(k4_subset_1(sK0,sK1,sK1),sK0) | r1_tarski(k4_subset_1(sK0,sK1,sK1),sK0)),
% 1.84/0.60    inference(resolution,[],[f300,f33])).
% 1.84/0.60  fof(f33,plain,(
% 1.84/0.60    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f16])).
% 1.84/0.60  fof(f300,plain,(
% 1.84/0.60    ( ! [X7] : (r2_hidden(sK2(k4_subset_1(sK0,sK1,sK1),X7),sK0) | r1_tarski(k4_subset_1(sK0,sK1,sK1),X7)) )),
% 1.84/0.60    inference(resolution,[],[f219,f74])).
% 1.84/0.60  fof(f74,plain,(
% 1.84/0.60    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 1.84/0.60    inference(resolution,[],[f31,f67])).
% 1.84/0.60  fof(f67,plain,(
% 1.84/0.60    r1_tarski(sK1,sK0)),
% 1.84/0.60    inference(resolution,[],[f65,f54])).
% 1.84/0.60  fof(f54,plain,(
% 1.84/0.60    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.84/0.60    inference(equality_resolution,[],[f35])).
% 1.84/0.60  fof(f35,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.84/0.60    inference(cnf_transformation,[],[f5])).
% 1.84/0.60  fof(f5,axiom,(
% 1.84/0.60    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.84/0.60  fof(f65,plain,(
% 1.84/0.60    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.84/0.60    inference(subsumption_resolution,[],[f61,f21])).
% 1.84/0.60  fof(f21,plain,(
% 1.84/0.60    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.84/0.60    inference(cnf_transformation,[],[f10])).
% 1.84/0.60  fof(f10,axiom,(
% 1.84/0.60    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.84/0.60  fof(f61,plain,(
% 1.84/0.60    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.84/0.60    inference(resolution,[],[f30,f19])).
% 1.84/0.60  fof(f30,plain,(
% 1.84/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f15])).
% 1.84/0.60  fof(f15,plain,(
% 1.84/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.84/0.60    inference(ennf_transformation,[],[f7])).
% 1.84/0.60  fof(f7,axiom,(
% 1.84/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.84/0.60  % (21945)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.84/0.60  fof(f219,plain,(
% 1.84/0.60    ( ! [X1] : (r2_hidden(sK2(k4_subset_1(sK0,sK1,sK1),X1),sK1) | r1_tarski(k4_subset_1(sK0,sK1,sK1),X1)) )),
% 1.84/0.60    inference(resolution,[],[f209,f32])).
% 1.84/0.60  fof(f32,plain,(
% 1.84/0.60    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f16])).
% 1.84/0.60  fof(f209,plain,(
% 1.84/0.60    ( ! [X2] : (~r2_hidden(X2,k4_subset_1(sK0,sK1,sK1)) | r2_hidden(X2,sK1)) )),
% 1.84/0.60    inference(duplicate_literal_removal,[],[f203])).
% 1.84/0.60  fof(f203,plain,(
% 1.84/0.60    ( ! [X2] : (~r2_hidden(X2,k4_subset_1(sK0,sK1,sK1)) | r2_hidden(X2,sK1) | r2_hidden(X2,sK1)) )),
% 1.84/0.60    inference(superposition,[],[f58,f197])).
% 1.84/0.60  fof(f58,plain,(
% 1.84/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_tarski(k1_enumset1(X0,X0,X1))) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 1.84/0.60    inference(equality_resolution,[],[f50])).
% 1.84/0.60  fof(f50,plain,(
% 1.84/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 1.84/0.60    inference(definition_unfolding,[],[f42,f45])).
% 1.84/0.60  fof(f42,plain,(
% 1.84/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.84/0.60    inference(cnf_transformation,[],[f2])).
% 1.84/0.60  fof(f733,plain,(
% 1.84/0.60    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(sK4(sK0,sK1,sK0),sK0)),
% 1.84/0.60    inference(duplicate_literal_removal,[],[f730])).
% 1.84/0.60  fof(f730,plain,(
% 1.84/0.60    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~r2_hidden(sK4(sK0,sK1,sK0),sK0) | sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.84/0.60    inference(resolution,[],[f640,f53])).
% 1.84/0.60  fof(f1034,plain,(
% 1.84/0.60    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.84/0.60    inference(forward_demodulation,[],[f1031,f46])).
% 1.84/0.60  fof(f46,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.84/0.60    inference(definition_unfolding,[],[f24,f26,f26])).
% 1.84/0.60  fof(f24,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f3])).
% 1.84/0.60  fof(f3,axiom,(
% 1.84/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.84/0.60  fof(f1031,plain,(
% 1.84/0.60    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK0))),
% 1.84/0.60    inference(resolution,[],[f132,f19])).
% 1.84/0.60  fof(f132,plain,(
% 1.84/0.60    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X2,X1,X2)) )),
% 1.84/0.60    inference(resolution,[],[f47,f60])).
% 1.84/0.60  fof(f60,plain,(
% 1.84/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.84/0.60    inference(forward_demodulation,[],[f23,f22])).
% 1.84/0.60  fof(f23,plain,(
% 1.84/0.60    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.84/0.60    inference(cnf_transformation,[],[f9])).
% 1.84/0.60  fof(f9,axiom,(
% 1.84/0.60    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.84/0.60  % SZS output end Proof for theBenchmark
% 1.84/0.60  % (21900)------------------------------
% 1.84/0.60  % (21900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (21900)Termination reason: Refutation
% 1.84/0.60  
% 1.84/0.60  % (21900)Memory used [KB]: 6908
% 1.84/0.60  % (21900)Time elapsed: 0.149 s
% 1.84/0.60  % (21900)------------------------------
% 1.84/0.60  % (21900)------------------------------
% 1.84/0.60  % (21893)Success in time 0.24 s
%------------------------------------------------------------------------------
