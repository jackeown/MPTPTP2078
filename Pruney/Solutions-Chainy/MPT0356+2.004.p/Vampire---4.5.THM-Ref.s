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
% DateTime   : Thu Dec  3 12:44:24 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 206 expanded)
%              Number of leaves         :   15 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  148 ( 545 expanded)
%              Number of equality atoms :   45 ( 113 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f651,plain,(
    $false ),
    inference(global_subsumption,[],[f116,f372,f624])).

fof(f624,plain,(
    r1_tarski(sK2,sK0) ),
    inference(superposition,[],[f34,f503])).

fof(f503,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f502,f194])).

fof(f194,plain,(
    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f96,f89])).

fof(f89,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
            & r1_tarski(X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
          & r1_tarski(sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
        & r1_tarski(sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f96,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f502,plain,(
    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f496,f89])).

fof(f496,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f90,f29])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = k4_xboole_0(X0,k3_subset_1(X0,X1)) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f372,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f60,f361])).

fof(f361,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f360,f222])).

fof(f222,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f141,f174])).

fof(f174,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f148,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f64,f34])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f43,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f148,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f48,f33])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f35,f36,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f141,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f47,f33])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f360,plain,(
    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f349,f174])).

fof(f349,plain,(
    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f154,f257])).

fof(f257,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f252,f104])).

fof(f104,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f101,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f101,plain,(
    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f30,f89])).

fof(f30,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f245,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f245,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f66,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f66,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k4_xboole_0(X2,X3))
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f43,f34])).

fof(f154,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f47,f48])).

fof(f60,plain,(
    ! [X2,X1] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(resolution,[],[f45,f49])).

fof(f116,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f46,f91])).

fof(f91,plain,(
    ~ r1_tarski(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f31,f88])).

fof(f88,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f39,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:49:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (3725)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.48  % (3731)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.44/0.55  % (3714)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.44/0.57  % (3738)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.44/0.57  % (3738)Refutation not found, incomplete strategy% (3738)------------------------------
% 1.44/0.57  % (3738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (3738)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (3738)Memory used [KB]: 6268
% 1.44/0.57  % (3738)Time elapsed: 0.160 s
% 1.44/0.57  % (3738)------------------------------
% 1.44/0.57  % (3738)------------------------------
% 1.44/0.58  % (3732)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.58  % (3717)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.44/0.58  % (3723)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.44/0.58  % (3710)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.44/0.58  % (3721)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.58  % (3739)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.44/0.58  % (3739)Refutation not found, incomplete strategy% (3739)------------------------------
% 1.44/0.58  % (3739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.58  % (3739)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.58  
% 1.44/0.58  % (3739)Memory used [KB]: 10746
% 1.44/0.58  % (3739)Time elapsed: 0.162 s
% 1.44/0.58  % (3739)------------------------------
% 1.44/0.58  % (3739)------------------------------
% 1.44/0.59  % (3726)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.44/0.59  % (3730)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.59  % (3734)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.44/0.59  % (3715)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.44/0.59  % (3723)Refutation not found, incomplete strategy% (3723)------------------------------
% 1.44/0.59  % (3723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.59  % (3723)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.59  
% 1.44/0.59  % (3723)Memory used [KB]: 10746
% 1.44/0.59  % (3723)Time elapsed: 0.088 s
% 1.44/0.59  % (3723)------------------------------
% 1.44/0.59  % (3723)------------------------------
% 1.44/0.59  % (3716)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.59  % (3712)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.44/0.59  % (3711)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.44/0.60  % (3711)Refutation not found, incomplete strategy% (3711)------------------------------
% 1.44/0.60  % (3711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.60  % (3711)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.60  
% 1.44/0.60  % (3711)Memory used [KB]: 1663
% 1.44/0.60  % (3711)Time elapsed: 0.171 s
% 1.44/0.60  % (3711)------------------------------
% 1.44/0.60  % (3711)------------------------------
% 1.44/0.60  % (3733)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.44/0.60  % (3727)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.61  % (3740)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.61  % (3740)Refutation not found, incomplete strategy% (3740)------------------------------
% 1.44/0.61  % (3740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.61  % (3740)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.61  
% 1.44/0.61  % (3740)Memory used [KB]: 1663
% 1.44/0.61  % (3740)Time elapsed: 0.002 s
% 1.44/0.61  % (3740)------------------------------
% 1.44/0.61  % (3740)------------------------------
% 1.44/0.61  % (3735)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.44/0.61  % (3713)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.44/0.61  % (3724)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.44/0.62  % (3716)Refutation found. Thanks to Tanya!
% 1.44/0.62  % SZS status Theorem for theBenchmark
% 1.44/0.62  % SZS output start Proof for theBenchmark
% 1.44/0.62  fof(f651,plain,(
% 1.44/0.62    $false),
% 1.44/0.62    inference(global_subsumption,[],[f116,f372,f624])).
% 1.44/0.62  fof(f624,plain,(
% 1.44/0.62    r1_tarski(sK2,sK0)),
% 1.44/0.62    inference(superposition,[],[f34,f503])).
% 1.44/0.62  fof(f503,plain,(
% 1.44/0.62    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.44/0.62    inference(forward_demodulation,[],[f502,f194])).
% 1.44/0.62  fof(f194,plain,(
% 1.44/0.62    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 1.44/0.62    inference(forward_demodulation,[],[f96,f89])).
% 1.44/0.62  fof(f89,plain,(
% 1.44/0.62    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.44/0.62    inference(resolution,[],[f39,f29])).
% 1.44/0.62  fof(f29,plain,(
% 1.44/0.62    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.44/0.62    inference(cnf_transformation,[],[f25])).
% 1.44/0.62  fof(f25,plain,(
% 1.44/0.62    (~r1_tarski(sK2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f24,f23])).
% 1.44/0.62  fof(f23,plain,(
% 1.44/0.62    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.44/0.62    introduced(choice_axiom,[])).
% 1.44/0.62  fof(f24,plain,(
% 1.44/0.62    ? [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(sK2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.44/0.62    introduced(choice_axiom,[])).
% 1.44/0.62  fof(f16,plain,(
% 1.44/0.62    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.62    inference(flattening,[],[f15])).
% 1.44/0.62  fof(f15,plain,(
% 1.44/0.62    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.62    inference(ennf_transformation,[],[f14])).
% 1.44/0.62  fof(f14,negated_conjecture,(
% 1.44/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.44/0.62    inference(negated_conjecture,[],[f13])).
% 1.44/0.62  fof(f13,conjecture,(
% 1.44/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 1.44/0.62  fof(f39,plain,(
% 1.44/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f18])).
% 1.44/0.62  fof(f18,plain,(
% 1.44/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.62    inference(ennf_transformation,[],[f10])).
% 1.44/0.62  fof(f10,axiom,(
% 1.44/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.44/0.62  fof(f96,plain,(
% 1.44/0.62    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 1.44/0.62    inference(resolution,[],[f40,f29])).
% 1.44/0.62  fof(f40,plain,(
% 1.44/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.44/0.62    inference(cnf_transformation,[],[f19])).
% 1.44/0.62  fof(f19,plain,(
% 1.44/0.62    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.62    inference(ennf_transformation,[],[f12])).
% 1.44/0.62  fof(f12,axiom,(
% 1.44/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.44/0.62  fof(f502,plain,(
% 1.44/0.62    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.44/0.62    inference(forward_demodulation,[],[f496,f89])).
% 1.44/0.62  fof(f496,plain,(
% 1.44/0.62    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))),
% 1.44/0.62    inference(resolution,[],[f90,f29])).
% 1.44/0.62  fof(f90,plain,(
% 1.44/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = k4_xboole_0(X0,k3_subset_1(X0,X1))) )),
% 1.44/0.62    inference(resolution,[],[f39,f38])).
% 1.44/0.62  fof(f38,plain,(
% 1.44/0.62    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.62    inference(cnf_transformation,[],[f17])).
% 1.44/0.62  fof(f17,plain,(
% 1.44/0.62    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.62    inference(ennf_transformation,[],[f11])).
% 1.44/0.62  fof(f11,axiom,(
% 1.44/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.44/0.62  fof(f34,plain,(
% 1.44/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f6])).
% 1.44/0.62  fof(f6,axiom,(
% 1.44/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.44/0.62  fof(f372,plain,(
% 1.44/0.62    r1_xboole_0(sK2,sK1)),
% 1.44/0.62    inference(superposition,[],[f60,f361])).
% 1.44/0.62  fof(f361,plain,(
% 1.44/0.62    sK2 = k4_xboole_0(sK2,sK1)),
% 1.44/0.62    inference(forward_demodulation,[],[f360,f222])).
% 1.44/0.62  fof(f222,plain,(
% 1.44/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.62    inference(forward_demodulation,[],[f141,f174])).
% 1.44/0.62  fof(f174,plain,(
% 1.44/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.44/0.62    inference(forward_demodulation,[],[f148,f81])).
% 1.44/0.62  fof(f81,plain,(
% 1.44/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.44/0.62    inference(resolution,[],[f64,f34])).
% 1.44/0.62  fof(f64,plain,(
% 1.44/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.44/0.62    inference(resolution,[],[f43,f32])).
% 1.44/0.62  fof(f32,plain,(
% 1.44/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f5])).
% 1.44/0.62  fof(f5,axiom,(
% 1.44/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.44/0.62  fof(f43,plain,(
% 1.44/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f27])).
% 1.44/0.62  fof(f27,plain,(
% 1.44/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.62    inference(flattening,[],[f26])).
% 1.44/0.62  fof(f26,plain,(
% 1.44/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.62    inference(nnf_transformation,[],[f2])).
% 1.44/0.62  fof(f2,axiom,(
% 1.44/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.62  fof(f148,plain,(
% 1.44/0.62    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.44/0.62    inference(superposition,[],[f48,f33])).
% 1.44/0.62  fof(f33,plain,(
% 1.44/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.62    inference(cnf_transformation,[],[f7])).
% 1.44/0.62  fof(f7,axiom,(
% 1.44/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.44/0.62  fof(f48,plain,(
% 1.44/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.44/0.62    inference(definition_unfolding,[],[f35,f36,f36])).
% 1.44/0.62  fof(f36,plain,(
% 1.44/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.44/0.62    inference(cnf_transformation,[],[f8])).
% 1.44/0.62  fof(f8,axiom,(
% 1.44/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.44/0.62  fof(f35,plain,(
% 1.44/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f1])).
% 1.44/0.62  fof(f1,axiom,(
% 1.44/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.44/0.62  fof(f141,plain,(
% 1.44/0.62    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.44/0.62    inference(superposition,[],[f47,f33])).
% 1.44/0.62  fof(f47,plain,(
% 1.44/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.44/0.62    inference(definition_unfolding,[],[f37,f36])).
% 1.44/0.62  fof(f37,plain,(
% 1.44/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.62    inference(cnf_transformation,[],[f3])).
% 1.44/0.62  fof(f3,axiom,(
% 1.44/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.44/0.62  fof(f360,plain,(
% 1.44/0.62    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0)),
% 1.44/0.62    inference(forward_demodulation,[],[f349,f174])).
% 1.44/0.62  fof(f349,plain,(
% 1.44/0.62    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k4_xboole_0(sK1,sK1))),
% 1.44/0.62    inference(superposition,[],[f154,f257])).
% 1.44/0.62  fof(f257,plain,(
% 1.44/0.62    sK1 = k4_xboole_0(sK1,sK2)),
% 1.44/0.62    inference(resolution,[],[f252,f104])).
% 1.44/0.62  fof(f104,plain,(
% 1.44/0.62    r1_xboole_0(sK1,sK2)),
% 1.44/0.62    inference(resolution,[],[f101,f45])).
% 1.44/0.62  fof(f45,plain,(
% 1.44/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f20])).
% 1.44/0.62  fof(f20,plain,(
% 1.44/0.62    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.44/0.62    inference(ennf_transformation,[],[f4])).
% 1.44/0.62  fof(f4,axiom,(
% 1.44/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.44/0.62  fof(f101,plain,(
% 1.44/0.62    r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 1.44/0.62    inference(backward_demodulation,[],[f30,f89])).
% 1.44/0.62  fof(f30,plain,(
% 1.44/0.62    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.44/0.62    inference(cnf_transformation,[],[f25])).
% 1.44/0.62  fof(f252,plain,(
% 1.44/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.44/0.62    inference(subsumption_resolution,[],[f245,f49])).
% 1.44/0.62  fof(f49,plain,(
% 1.44/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.44/0.62    inference(equality_resolution,[],[f42])).
% 1.44/0.62  fof(f42,plain,(
% 1.44/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.44/0.62    inference(cnf_transformation,[],[f27])).
% 1.44/0.62  fof(f245,plain,(
% 1.44/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X0)) )),
% 1.44/0.62    inference(resolution,[],[f66,f46])).
% 1.44/0.62  fof(f46,plain,(
% 1.44/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f22])).
% 1.44/0.62  fof(f22,plain,(
% 1.44/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.44/0.62    inference(flattening,[],[f21])).
% 1.44/0.62  fof(f21,plain,(
% 1.44/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.44/0.62    inference(ennf_transformation,[],[f9])).
% 1.44/0.62  fof(f9,axiom,(
% 1.44/0.62    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.44/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.44/0.62  fof(f66,plain,(
% 1.44/0.62    ( ! [X2,X3] : (~r1_tarski(X2,k4_xboole_0(X2,X3)) | k4_xboole_0(X2,X3) = X2) )),
% 1.44/0.62    inference(resolution,[],[f43,f34])).
% 1.44/0.62  fof(f154,plain,(
% 1.44/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.44/0.62    inference(superposition,[],[f47,f48])).
% 1.44/0.62  fof(f60,plain,(
% 1.44/0.62    ( ! [X2,X1] : (r1_xboole_0(k4_xboole_0(X1,X2),X2)) )),
% 1.44/0.62    inference(resolution,[],[f45,f49])).
% 1.44/0.62  fof(f116,plain,(
% 1.44/0.62    ~r1_xboole_0(sK2,sK1) | ~r1_tarski(sK2,sK0)),
% 1.44/0.62    inference(resolution,[],[f46,f91])).
% 1.44/0.62  fof(f91,plain,(
% 1.44/0.62    ~r1_tarski(sK2,k4_xboole_0(sK0,sK1))),
% 1.44/0.62    inference(backward_demodulation,[],[f31,f88])).
% 1.44/0.62  fof(f88,plain,(
% 1.44/0.62    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.44/0.62    inference(resolution,[],[f39,f28])).
% 1.44/0.62  fof(f28,plain,(
% 1.44/0.62    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.62    inference(cnf_transformation,[],[f25])).
% 1.44/0.62  fof(f31,plain,(
% 1.44/0.62    ~r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 1.44/0.62    inference(cnf_transformation,[],[f25])).
% 1.44/0.62  % SZS output end Proof for theBenchmark
% 1.44/0.62  % (3716)------------------------------
% 1.44/0.62  % (3716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.62  % (3716)Termination reason: Refutation
% 1.44/0.62  
% 1.44/0.62  % (3716)Memory used [KB]: 11129
% 1.44/0.62  % (3716)Time elapsed: 0.204 s
% 1.44/0.62  % (3716)------------------------------
% 1.44/0.62  % (3716)------------------------------
% 1.44/0.62  % (3718)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.44/0.62  % (3727)Refutation not found, incomplete strategy% (3727)------------------------------
% 1.44/0.62  % (3727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.62  % (3737)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.44/0.62  % (3727)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.62  
% 1.44/0.62  % (3727)Memory used [KB]: 10618
% 1.44/0.62  % (3727)Time elapsed: 0.190 s
% 1.44/0.62  % (3727)------------------------------
% 1.44/0.62  % (3727)------------------------------
% 2.08/0.63  % (3737)Refutation not found, incomplete strategy% (3737)------------------------------
% 2.08/0.63  % (3737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.63  % (3737)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.63  
% 2.08/0.63  % (3737)Memory used [KB]: 6268
% 2.08/0.63  % (3737)Time elapsed: 0.199 s
% 2.08/0.63  % (3737)------------------------------
% 2.08/0.63  % (3737)------------------------------
% 2.08/0.63  % (3736)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.08/0.63  % (3729)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.08/0.63  % (3736)Refutation not found, incomplete strategy% (3736)------------------------------
% 2.08/0.63  % (3736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.63  % (3736)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.63  
% 2.08/0.63  % (3736)Memory used [KB]: 6268
% 2.08/0.63  % (3736)Time elapsed: 0.197 s
% 2.08/0.63  % (3736)------------------------------
% 2.08/0.63  % (3736)------------------------------
% 2.08/0.63  % (3729)Refutation not found, incomplete strategy% (3729)------------------------------
% 2.08/0.63  % (3729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.63  % (3729)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.63  
% 2.08/0.63  % (3729)Memory used [KB]: 1663
% 2.08/0.63  % (3729)Time elapsed: 0.196 s
% 2.08/0.63  % (3729)------------------------------
% 2.08/0.63  % (3729)------------------------------
% 2.08/0.63  % (3708)Success in time 0.265 s
%------------------------------------------------------------------------------
