%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 225 expanded)
%              Number of leaves         :    5 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  152 (1284 expanded)
%              Number of equality atoms :  135 (1155 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(global_subsumption,[],[f58,f61])).

fof(f61,plain,(
    sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(forward_demodulation,[],[f60,f17])).

fof(f17,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f60,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k4_tarski(sK5,sK6)) ),
    inference(forward_demodulation,[],[f59,f33])).

fof(f33,plain,(
    k4_tarski(sK5,sK6) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f17,f31])).

fof(f31,plain,(
    k4_tarski(k4_tarski(sK5,sK6),sK7) = k1_mcart_1(sK4) ),
    inference(superposition,[],[f17,f26])).

fof(f26,plain,(
    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8) ),
    inference(definition_unfolding,[],[f11,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f11,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
       => ~ ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f59,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(unit_resulting_resolution,[],[f13,f14,f16,f15,f25,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f25,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f12,f20])).

fof(f12,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f14,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(global_subsumption,[],[f47,f55])).

fof(f55,plain,(
    sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(forward_demodulation,[],[f54,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f4])).

fof(f54,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k4_tarski(sK5,sK6)) ),
    inference(forward_demodulation,[],[f52,f33])).

fof(f52,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(unit_resulting_resolution,[],[f13,f14,f16,f15,f25,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,
    ( sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(global_subsumption,[],[f38,f46])).

fof(f46,plain,
    ( sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,
    ( sK7 != sK7
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f10,f44])).

fof(f44,plain,(
    sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(forward_demodulation,[],[f42,f35])).

fof(f35,plain,(
    sK7 = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f18,f31])).

% (12811)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f42,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f13,f14,f16,f15,f25,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,plain,
    ( sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(forward_demodulation,[],[f36,f34])).

fof(f34,plain,(
    sK8 = k2_mcart_1(sK4) ),
    inference(superposition,[],[f18,f32])).

fof(f32,plain,(
    sK4 = k4_tarski(k1_mcart_1(sK4),sK8) ),
    inference(backward_demodulation,[],[f26,f31])).

fof(f36,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    inference(unit_resulting_resolution,[],[f14,f13,f16,f15,f25,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:36:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (12816)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.49  % (12807)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (12816)Refutation not found, incomplete strategy% (12816)------------------------------
% 0.21/0.49  % (12816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12816)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12816)Memory used [KB]: 1791
% 0.21/0.49  % (12816)Time elapsed: 0.063 s
% 0.21/0.49  % (12816)------------------------------
% 0.21/0.49  % (12816)------------------------------
% 0.21/0.49  % (12807)Refutation not found, incomplete strategy% (12807)------------------------------
% 0.21/0.49  % (12807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12807)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12807)Memory used [KB]: 6140
% 0.21/0.49  % (12807)Time elapsed: 0.003 s
% 0.21/0.49  % (12807)------------------------------
% 0.21/0.49  % (12807)------------------------------
% 0.21/0.50  % (12799)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (12803)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (12817)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.50  % (12795)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (12817)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(global_subsumption,[],[f58,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.51    inference(forward_demodulation,[],[f60,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k4_tarski(sK5,sK6))),
% 0.21/0.51    inference(forward_demodulation,[],[f59,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    k4_tarski(sK5,sK6) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.51    inference(superposition,[],[f17,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    k4_tarski(k4_tarski(sK5,sK6),sK7) = k1_mcart_1(sK4)),
% 0.21/0.51    inference(superposition,[],[f17,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8)),
% 0.21/0.51    inference(definition_unfolding,[],[f11,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.51    inference(flattening,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4] : ((? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f13,f14,f16,f15,f25,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f21,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.51    inference(definition_unfolding,[],[f12,f20])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    k1_xboole_0 != sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    k1_xboole_0 != sK3),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.51    inference(global_subsumption,[],[f47,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.51    inference(forward_demodulation,[],[f54,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k4_tarski(sK5,sK6))),
% 0.21/0.51    inference(forward_demodulation,[],[f52,f33])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f13,f14,f16,f15,f25,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f22,f20])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.51    inference(global_subsumption,[],[f38,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    sK7 != sK7 | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.51    inference(backward_demodulation,[],[f10,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.51    inference(forward_demodulation,[],[f42,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    sK7 = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.51    inference(superposition,[],[f18,f31])).
% 0.21/0.51  % (12811)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f13,f14,f16,f15,f25,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f23,f20])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.51    inference(forward_demodulation,[],[f36,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    sK8 = k2_mcart_1(sK4)),
% 0.21/0.51    inference(superposition,[],[f18,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    sK4 = k4_tarski(k1_mcart_1(sK4),sK8)),
% 0.21/0.51    inference(backward_demodulation,[],[f26,f31])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f14,f13,f16,f15,f25,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f24,f20])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (12817)------------------------------
% 0.21/0.51  % (12817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12817)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12817)Memory used [KB]: 6268
% 0.21/0.51  % (12817)Time elapsed: 0.088 s
% 0.21/0.51  % (12817)------------------------------
% 0.21/0.51  % (12817)------------------------------
% 0.21/0.51  % (12789)Success in time 0.153 s
%------------------------------------------------------------------------------
