%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   46 (  82 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 173 expanded)
%              Number of equality atoms :   27 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f19,f20,f18,f35,f105])).

fof(f105,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5)))
      | ~ v1_zfmisc_1(X4)
      | r1_tarski(X4,X5)
      | v1_xboole_0(X4) ) ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X4,X5)
      | ~ v1_zfmisc_1(X4)
      | v1_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5)))
      | v1_xboole_0(X4) ) ),
    inference(forward_demodulation,[],[f102,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
      | k1_xboole_0 = k5_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f39,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f23,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f33])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f102,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k5_xboole_0(X4,X4)
      | r1_tarski(X4,X5)
      | ~ v1_zfmisc_1(X4)
      | v1_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5)))
      | v1_xboole_0(X4) ) ),
    inference(superposition,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X1] :
      ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f21,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f22,f33])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ~ v1_xboole_0(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f33])).

fof(f17,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(f18,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:20:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (11091)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (11099)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (11091)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % (11107)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f106,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f19,f20,f18,f35,f105])).
% 1.34/0.54  fof(f105,plain,(
% 1.34/0.54    ( ! [X4,X5] : (v1_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5))) | ~v1_zfmisc_1(X4) | r1_tarski(X4,X5) | v1_xboole_0(X4)) )),
% 1.34/0.54    inference(trivial_inequality_removal,[],[f104])).
% 1.34/0.54  fof(f104,plain,(
% 1.34/0.54    ( ! [X4,X5] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X4,X5) | ~v1_zfmisc_1(X4) | v1_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5))) | v1_xboole_0(X4)) )),
% 1.34/0.54    inference(forward_demodulation,[],[f102,f64])).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.34/0.54    inference(resolution,[],[f62,f42])).
% 1.34/0.54  fof(f42,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.34/0.54    inference(resolution,[],[f32,f40])).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.54    inference(equality_resolution,[],[f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f16])).
% 1.34/0.54  fof(f16,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.34/0.54    inference(ennf_transformation,[],[f4])).
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.34/0.54  fof(f62,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_xboole_0(X0,X1)) | k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.34/0.54    inference(superposition,[],[f39,f37])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k2_xboole_0(X0,X1))) = X0) )),
% 1.34/0.54    inference(definition_unfolding,[],[f23,f33])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.34/0.54    inference(definition_unfolding,[],[f24,f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~r1_tarski(X0,X1)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f30,f34])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 1.34/0.54    inference(definition_unfolding,[],[f26,f33])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f2])).
% 1.34/0.54  fof(f2,axiom,(
% 1.34/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.34/0.54  fof(f102,plain,(
% 1.34/0.54    ( ! [X4,X5] : (k1_xboole_0 != k5_xboole_0(X4,X4) | r1_tarski(X4,X5) | ~v1_zfmisc_1(X4) | v1_xboole_0(k1_setfam_1(k1_enumset1(X4,X4,X5))) | v1_xboole_0(X4)) )),
% 1.34/0.54    inference(superposition,[],[f38,f55])).
% 1.34/0.54  fof(f55,plain,(
% 1.34/0.54    ( ! [X2,X1] : (k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(k1_setfam_1(k1_enumset1(X1,X1,X2))) | v1_xboole_0(X1)) )),
% 1.34/0.54    inference(resolution,[],[f21,f36])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f22,f33])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.34/0.54  fof(f21,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X0) | X0 = X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f15])).
% 1.34/0.54  fof(f15,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.34/0.54    inference(flattening,[],[f14])).
% 1.34/0.54  fof(f14,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f31,f34])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f2])).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    ~v1_xboole_0(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 1.34/0.54    inference(definition_unfolding,[],[f17,f33])).
% 1.34/0.54  fof(f17,plain,(
% 1.34/0.54    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 1.34/0.54    inference(cnf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,plain,(
% 1.34/0.54    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 1.34/0.54    inference(flattening,[],[f12])).
% 1.34/0.54  fof(f12,plain,(
% 1.34/0.54    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,negated_conjecture,(
% 1.34/0.54    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.34/0.54    inference(negated_conjecture,[],[f10])).
% 1.34/0.54  fof(f10,conjecture,(
% 1.34/0.54    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ~r1_tarski(sK0,sK1)),
% 1.34/0.54    inference(cnf_transformation,[],[f13])).
% 1.34/0.54  fof(f20,plain,(
% 1.34/0.54    v1_zfmisc_1(sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f13])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ~v1_xboole_0(sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f13])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (11091)------------------------------
% 1.34/0.54  % (11091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (11091)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (11091)Memory used [KB]: 6268
% 1.34/0.54  % (11091)Time elapsed: 0.111 s
% 1.34/0.54  % (11091)------------------------------
% 1.34/0.54  % (11091)------------------------------
% 1.34/0.55  % (11077)Success in time 0.179 s
%------------------------------------------------------------------------------
