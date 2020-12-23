%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   42 (  64 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 163 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f127,f81,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f81,plain,(
    ! [X4] : r1_tarski(k9_subset_1(sK0,X4,sK2),X4) ),
    inference(superposition,[],[f37,f51])).

fof(f51,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f32,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

% (2741)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (2722)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f18,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f35,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f35,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f127,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(forward_demodulation,[],[f126,f41])).

fof(f41,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f126,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f44,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(sK0,X0,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f23,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f44,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))
    | ~ m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f24,f26])).

fof(f24,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:57:21 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.52  % (2714)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (2724)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (2723)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (2732)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (2737)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (2715)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (2729)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (2724)Refutation not found, incomplete strategy% (2724)------------------------------
% 0.22/0.54  % (2724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2716)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (2738)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (2724)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2724)Memory used [KB]: 10746
% 0.22/0.54  % (2724)Time elapsed: 0.116 s
% 0.22/0.54  % (2724)------------------------------
% 0.22/0.54  % (2724)------------------------------
% 0.22/0.54  % (2720)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (2717)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (2718)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (2718)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f127,f81,f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X4] : (r1_tarski(k9_subset_1(sK0,X4,sK2),X4)) )),
% 0.22/0.55    inference(superposition,[],[f37,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X0] : (k9_subset_1(sK0,X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2))) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f23,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f32,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  % (2741)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.39/0.55  % (2722)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.55  fof(f18,plain,(
% 1.39/0.55    ? [X2] : (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f11,plain,(
% 1.39/0.55    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f9])).
% 1.39/0.55  fof(f9,negated_conjecture,(
% 1.39/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 1.39/0.55    inference(negated_conjecture,[],[f8])).
% 1.39/0.55  fof(f8,conjecture,(
% 1.39/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f35,f33])).
% 1.39/0.55  fof(f33,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f16])).
% 1.39/0.55  fof(f16,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.39/0.55    inference(ennf_transformation,[],[f10])).
% 1.39/0.55  fof(f10,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.39/0.55    inference(pure_predicate_removal,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.39/0.55  fof(f35,plain,(
% 1.39/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f28])).
% 1.39/0.55  fof(f28,plain,(
% 1.39/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f21])).
% 1.39/0.55  fof(f21,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(flattening,[],[f20])).
% 1.39/0.55  fof(f20,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f1])).
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.55  fof(f127,plain,(
% 1.39/0.55    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 1.39/0.55    inference(forward_demodulation,[],[f126,f41])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f22,f26])).
% 1.39/0.55  fof(f26,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f12])).
% 1.39/0.55  fof(f12,plain,(
% 1.39/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f5])).
% 1.39/0.55  fof(f5,axiom,(
% 1.39/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.39/0.55  fof(f22,plain,(
% 1.39/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.39/0.55    inference(cnf_transformation,[],[f19])).
% 1.39/0.55  fof(f126,plain,(
% 1.39/0.55    ~r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 1.39/0.55    inference(subsumption_resolution,[],[f44,f47])).
% 1.39/0.55  fof(f47,plain,(
% 1.39/0.55    ( ! [X0] : (m1_subset_1(k9_subset_1(sK0,X0,sK2),k1_zfmisc_1(sK0))) )),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f23,f31])).
% 1.39/0.55  fof(f31,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f14])).
% 1.39/0.55  fof(f14,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f6])).
% 1.39/0.55  fof(f6,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.39/0.55  fof(f44,plain,(
% 1.39/0.55    ~r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) | ~m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.39/0.55    inference(superposition,[],[f24,f26])).
% 1.39/0.55  fof(f24,plain,(
% 1.39/0.55    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 1.39/0.55    inference(cnf_transformation,[],[f19])).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (2718)------------------------------
% 1.39/0.55  % (2718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (2718)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (2718)Memory used [KB]: 1791
% 1.39/0.55  % (2718)Time elapsed: 0.130 s
% 1.39/0.55  % (2718)------------------------------
% 1.39/0.55  % (2718)------------------------------
% 1.39/0.55  % (2743)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.55  % (2734)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.55  % (2713)Success in time 0.185 s
%------------------------------------------------------------------------------
