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
% DateTime   : Thu Dec  3 12:44:21 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 543 expanded)
%              Number of leaves         :   15 ( 182 expanded)
%              Depth                    :   17
%              Number of atoms          :  121 ( 806 expanded)
%              Number of equality atoms :   62 ( 454 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1660,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1655,f683])).

fof(f683,plain,(
    k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) != k6_subset_1(sK1,sK2) ),
    inference(backward_demodulation,[],[f257,f664])).

fof(f664,plain,(
    ! [X20] : k7_subset_1(sK0,sK1,X20) = k6_subset_1(sK1,X20) ),
    inference(resolution,[],[f57,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f47,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f257,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f25,f256])).

fof(f256,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f239,f149])).

fof(f149,plain,(
    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f51,f83])).

fof(f83,plain,(
    sK2 = k6_subset_1(sK0,k6_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f74,f50])).

fof(f50,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f48,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f32,f31,f31])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f74,plain,(
    sK2 = k6_subset_1(sK2,k6_subset_1(sK2,sK0)) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f67,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f67,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f62,f27])).

fof(f27,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f62,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f37,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f31,f48])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f239,plain,(
    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) ),
    inference(resolution,[],[f53,f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f31])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f25,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f1655,plain,(
    k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) = k6_subset_1(sK1,sK2) ),
    inference(superposition,[],[f1266,f149])).

fof(f1266,plain,(
    ! [X15] : k9_subset_1(sK0,sK1,k6_subset_1(sK0,X15)) = k6_subset_1(sK1,X15) ),
    inference(forward_demodulation,[],[f1265,f454])).

fof(f454,plain,(
    ! [X7] : k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),X7)) = k6_subset_1(sK1,X7) ),
    inference(superposition,[],[f54,f161])).

fof(f161,plain,(
    sK1 = k6_subset_1(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f93,f150])).

fof(f150,plain,(
    k6_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f51,f93])).

fof(f93,plain,(
    sK1 = k6_subset_1(sK0,k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f75,f50])).

fof(f75,plain,(
    sK1 = k6_subset_1(sK1,k6_subset_1(sK1,sK0)) ),
    inference(resolution,[],[f52,f71])).

fof(f71,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f68,f58])).

fof(f68,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f63,f27])).

fof(f63,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f37,f26])).

fof(f54,plain,(
    ! [X2,X0,X1] : k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f44,f31,f31,f31])).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1265,plain,(
    ! [X15] : k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),X15)) = k9_subset_1(sK0,sK1,k6_subset_1(sK0,X15)) ),
    inference(forward_demodulation,[],[f1264,f1033])).

fof(f1033,plain,(
    ! [X2,X0,X1] : k9_subset_1(X0,X1,k6_subset_1(X0,X2)) = k3_subset_1(X1,k6_subset_1(X1,k6_subset_1(X0,X2))) ),
    inference(resolution,[],[f248,f29])).

fof(f29,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f248,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_subset_1(X1,k6_subset_1(X1,X2)) ) ),
    inference(backward_demodulation,[],[f56,f238])).

% (21064)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
fof(f238,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(resolution,[],[f53,f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k6_subset_1(X1,k6_subset_1(X1,X2)) ) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1264,plain,(
    ! [X15] : k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),X15)) = k3_subset_1(sK1,k6_subset_1(sK1,k6_subset_1(sK0,X15))) ),
    inference(forward_demodulation,[],[f1263,f238])).

fof(f1263,plain,(
    ! [X15] : k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),X15)) = k6_subset_1(sK1,k6_subset_1(sK1,k6_subset_1(sK0,X15))) ),
    inference(forward_demodulation,[],[f1173,f454])).

fof(f1173,plain,(
    ! [X15] : k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),X15)) = k6_subset_1(sK1,k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),k6_subset_1(sK0,X15)))) ),
    inference(superposition,[],[f60,f161])).

fof(f60,plain,(
    ! [X2,X0,X1] : k6_subset_1(X0,k2_xboole_0(X1,X2)) = k6_subset_1(k6_subset_1(X0,X1),k6_subset_1(X0,k2_xboole_0(X1,k6_subset_1(X0,X2)))) ),
    inference(forward_demodulation,[],[f55,f54])).

fof(f55,plain,(
    ! [X2,X0,X1] : k6_subset_1(X0,k2_xboole_0(X1,X2)) = k6_subset_1(k6_subset_1(X0,X1),k6_subset_1(k6_subset_1(X0,X1),k6_subset_1(X0,X2))) ),
    inference(definition_unfolding,[],[f45,f31,f48,f31,f31])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (21046)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (21037)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21053)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (21033)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (21028)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (21027)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (21026)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (21045)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (21049)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (21030)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (21044)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (21045)Refutation not found, incomplete strategy% (21045)------------------------------
% 0.21/0.53  % (21045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21045)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21045)Memory used [KB]: 10874
% 0.21/0.53  % (21045)Time elapsed: 0.121 s
% 0.21/0.53  % (21045)------------------------------
% 0.21/0.53  % (21045)------------------------------
% 0.21/0.53  % (21031)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (21050)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (21029)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (21034)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (21048)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (21042)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (21052)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (21025)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (21035)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (21042)Refutation not found, incomplete strategy% (21042)------------------------------
% 0.21/0.54  % (21042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21042)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21042)Memory used [KB]: 10618
% 0.21/0.54  % (21042)Time elapsed: 0.090 s
% 0.21/0.54  % (21042)------------------------------
% 0.21/0.54  % (21042)------------------------------
% 0.21/0.54  % (21025)Refutation not found, incomplete strategy% (21025)------------------------------
% 0.21/0.54  % (21025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21025)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21025)Memory used [KB]: 1791
% 0.21/0.54  % (21025)Time elapsed: 0.126 s
% 0.21/0.54  % (21025)------------------------------
% 0.21/0.54  % (21025)------------------------------
% 0.21/0.54  % (21029)Refutation not found, incomplete strategy% (21029)------------------------------
% 0.21/0.54  % (21029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21029)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21029)Memory used [KB]: 6396
% 0.21/0.54  % (21029)Time elapsed: 0.132 s
% 0.21/0.54  % (21029)------------------------------
% 0.21/0.54  % (21029)------------------------------
% 0.21/0.54  % (21054)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (21043)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (21051)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (21032)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.43/0.54  % (21038)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.54  % (21041)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.54  % (21035)Refutation not found, incomplete strategy% (21035)------------------------------
% 1.43/0.54  % (21035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (21035)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (21035)Memory used [KB]: 10618
% 1.43/0.54  % (21035)Time elapsed: 0.127 s
% 1.43/0.54  % (21035)------------------------------
% 1.43/0.54  % (21035)------------------------------
% 1.43/0.54  % (21036)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.55  % (21040)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.43/0.55  % (21034)Refutation not found, incomplete strategy% (21034)------------------------------
% 1.43/0.55  % (21034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (21036)Refutation not found, incomplete strategy% (21036)------------------------------
% 1.43/0.55  % (21036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (21039)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.55  % (21040)Refutation not found, incomplete strategy% (21040)------------------------------
% 1.43/0.55  % (21040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (21040)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (21040)Memory used [KB]: 6140
% 1.43/0.55  % (21040)Time elapsed: 0.003 s
% 1.43/0.55  % (21040)------------------------------
% 1.43/0.55  % (21040)------------------------------
% 1.43/0.55  % (21034)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (21034)Memory used [KB]: 10746
% 1.43/0.55  % (21034)Time elapsed: 0.106 s
% 1.43/0.55  % (21034)------------------------------
% 1.43/0.55  % (21034)------------------------------
% 1.43/0.55  % (21036)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (21036)Memory used [KB]: 10618
% 1.43/0.55  % (21036)Time elapsed: 0.141 s
% 1.43/0.55  % (21036)------------------------------
% 1.43/0.55  % (21036)------------------------------
% 1.43/0.56  % (21047)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.60/0.56  % (21047)Refutation not found, incomplete strategy% (21047)------------------------------
% 1.60/0.56  % (21047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (21047)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (21047)Memory used [KB]: 10746
% 1.60/0.57  % (21047)Time elapsed: 0.162 s
% 1.60/0.57  % (21047)------------------------------
% 1.60/0.57  % (21047)------------------------------
% 1.99/0.64  % (21031)Refutation found. Thanks to Tanya!
% 1.99/0.64  % SZS status Theorem for theBenchmark
% 1.99/0.66  % SZS output start Proof for theBenchmark
% 1.99/0.66  fof(f1660,plain,(
% 1.99/0.66    $false),
% 1.99/0.66    inference(subsumption_resolution,[],[f1655,f683])).
% 1.99/0.66  fof(f683,plain,(
% 1.99/0.66    k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) != k6_subset_1(sK1,sK2)),
% 1.99/0.66    inference(backward_demodulation,[],[f257,f664])).
% 1.99/0.66  fof(f664,plain,(
% 1.99/0.66    ( ! [X20] : (k7_subset_1(sK0,sK1,X20) = k6_subset_1(sK1,X20)) )),
% 1.99/0.66    inference(resolution,[],[f57,f26])).
% 1.99/0.66  fof(f26,plain,(
% 1.99/0.66    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.99/0.66    inference(cnf_transformation,[],[f18])).
% 1.99/0.66  fof(f18,plain,(
% 1.99/0.66    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.66    inference(ennf_transformation,[],[f17])).
% 1.99/0.66  fof(f17,negated_conjecture,(
% 1.99/0.66    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.99/0.66    inference(negated_conjecture,[],[f16])).
% 1.99/0.66  fof(f16,conjecture,(
% 1.99/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 1.99/0.66  fof(f57,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 1.99/0.66    inference(definition_unfolding,[],[f47,f31])).
% 1.99/0.66  fof(f31,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f13])).
% 1.99/0.66  fof(f13,axiom,(
% 1.99/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.99/0.66  fof(f47,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f23])).
% 1.99/0.66  fof(f23,plain,(
% 1.99/0.66    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.66    inference(ennf_transformation,[],[f14])).
% 1.99/0.66  fof(f14,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.99/0.66  fof(f257,plain,(
% 1.99/0.66    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))),
% 1.99/0.66    inference(backward_demodulation,[],[f25,f256])).
% 1.99/0.66  fof(f256,plain,(
% 1.99/0.66    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 1.99/0.66    inference(forward_demodulation,[],[f239,f149])).
% 1.99/0.66  fof(f149,plain,(
% 1.99/0.66    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 1.99/0.66    inference(superposition,[],[f51,f83])).
% 1.99/0.66  fof(f83,plain,(
% 1.99/0.66    sK2 = k6_subset_1(sK0,k6_subset_1(sK0,sK2))),
% 1.99/0.66    inference(superposition,[],[f74,f50])).
% 1.99/0.66  fof(f50,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f30,f48,f48])).
% 1.99/0.66  fof(f48,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f32,f31,f31])).
% 1.99/0.66  fof(f32,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f6])).
% 1.99/0.66  fof(f6,axiom,(
% 1.99/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.99/0.66  fof(f30,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f1])).
% 1.99/0.66  fof(f1,axiom,(
% 1.99/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.99/0.66  fof(f74,plain,(
% 1.99/0.66    sK2 = k6_subset_1(sK2,k6_subset_1(sK2,sK0))),
% 1.99/0.66    inference(resolution,[],[f52,f70])).
% 1.99/0.66  fof(f70,plain,(
% 1.99/0.66    r1_tarski(sK2,sK0)),
% 1.99/0.66    inference(resolution,[],[f67,f58])).
% 1.99/0.66  fof(f58,plain,(
% 1.99/0.66    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.99/0.66    inference(equality_resolution,[],[f41])).
% 1.99/0.66  fof(f41,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.99/0.66    inference(cnf_transformation,[],[f8])).
% 1.99/0.66  fof(f8,axiom,(
% 1.99/0.66    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.99/0.66  fof(f67,plain,(
% 1.99/0.66    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.99/0.66    inference(subsumption_resolution,[],[f62,f27])).
% 1.99/0.66  fof(f27,plain,(
% 1.99/0.66    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f12])).
% 1.99/0.66  fof(f12,axiom,(
% 1.99/0.66    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.99/0.66  fof(f62,plain,(
% 1.99/0.66    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.99/0.66    inference(resolution,[],[f37,f24])).
% 1.99/0.66  fof(f24,plain,(
% 1.99/0.66    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.99/0.66    inference(cnf_transformation,[],[f18])).
% 1.99/0.66  fof(f37,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f19])).
% 1.99/0.66  fof(f19,plain,(
% 1.99/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.99/0.66    inference(ennf_transformation,[],[f9])).
% 1.99/0.66  fof(f9,axiom,(
% 1.99/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.99/0.66  fof(f52,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0) )),
% 1.99/0.66    inference(definition_unfolding,[],[f38,f48])).
% 1.99/0.66  fof(f38,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.99/0.66    inference(cnf_transformation,[],[f20])).
% 1.99/0.66  fof(f20,plain,(
% 1.99/0.66    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.99/0.66    inference(ennf_transformation,[],[f3])).
% 1.99/0.66  fof(f3,axiom,(
% 1.99/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.99/0.66  fof(f51,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f33,f31,f48])).
% 1.99/0.66  fof(f33,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f2])).
% 1.99/0.66  fof(f2,axiom,(
% 1.99/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.99/0.66  fof(f239,plain,(
% 1.99/0.66    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)),
% 1.99/0.66    inference(resolution,[],[f53,f24])).
% 1.99/0.66  fof(f53,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.99/0.66    inference(definition_unfolding,[],[f39,f31])).
% 1.99/0.66  fof(f39,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f21])).
% 1.99/0.66  fof(f21,plain,(
% 1.99/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.66    inference(ennf_transformation,[],[f10])).
% 1.99/0.66  fof(f10,axiom,(
% 1.99/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.99/0.66  fof(f25,plain,(
% 1.99/0.66    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.99/0.66    inference(cnf_transformation,[],[f18])).
% 1.99/0.66  fof(f1655,plain,(
% 1.99/0.66    k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) = k6_subset_1(sK1,sK2)),
% 1.99/0.66    inference(superposition,[],[f1266,f149])).
% 1.99/0.66  fof(f1266,plain,(
% 1.99/0.66    ( ! [X15] : (k9_subset_1(sK0,sK1,k6_subset_1(sK0,X15)) = k6_subset_1(sK1,X15)) )),
% 1.99/0.66    inference(forward_demodulation,[],[f1265,f454])).
% 1.99/0.66  fof(f454,plain,(
% 1.99/0.66    ( ! [X7] : (k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),X7)) = k6_subset_1(sK1,X7)) )),
% 1.99/0.66    inference(superposition,[],[f54,f161])).
% 1.99/0.66  fof(f161,plain,(
% 1.99/0.66    sK1 = k6_subset_1(sK0,k5_xboole_0(sK0,sK1))),
% 1.99/0.66    inference(backward_demodulation,[],[f93,f150])).
% 1.99/0.66  fof(f150,plain,(
% 1.99/0.66    k6_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.99/0.66    inference(superposition,[],[f51,f93])).
% 1.99/0.66  fof(f93,plain,(
% 1.99/0.66    sK1 = k6_subset_1(sK0,k6_subset_1(sK0,sK1))),
% 1.99/0.66    inference(superposition,[],[f75,f50])).
% 1.99/0.66  fof(f75,plain,(
% 1.99/0.66    sK1 = k6_subset_1(sK1,k6_subset_1(sK1,sK0))),
% 1.99/0.66    inference(resolution,[],[f52,f71])).
% 1.99/0.66  fof(f71,plain,(
% 1.99/0.66    r1_tarski(sK1,sK0)),
% 1.99/0.66    inference(resolution,[],[f68,f58])).
% 1.99/0.66  fof(f68,plain,(
% 1.99/0.66    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.99/0.66    inference(subsumption_resolution,[],[f63,f27])).
% 1.99/0.66  fof(f63,plain,(
% 1.99/0.66    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.99/0.66    inference(resolution,[],[f37,f26])).
% 1.99/0.66  fof(f54,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k2_xboole_0(X1,X2))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f44,f31,f31,f31])).
% 1.99/0.66  fof(f44,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f5])).
% 1.99/0.66  fof(f5,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.99/0.66  fof(f1265,plain,(
% 1.99/0.66    ( ! [X15] : (k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),X15)) = k9_subset_1(sK0,sK1,k6_subset_1(sK0,X15))) )),
% 1.99/0.66    inference(forward_demodulation,[],[f1264,f1033])).
% 1.99/0.66  fof(f1033,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k6_subset_1(X0,X2)) = k3_subset_1(X1,k6_subset_1(X1,k6_subset_1(X0,X2)))) )),
% 1.99/0.66    inference(resolution,[],[f248,f29])).
% 1.99/0.66  fof(f29,plain,(
% 1.99/0.66    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f11])).
% 1.99/0.66  fof(f11,axiom,(
% 1.99/0.66    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.99/0.66  fof(f248,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_subset_1(X1,k6_subset_1(X1,X2))) )),
% 1.99/0.66    inference(backward_demodulation,[],[f56,f238])).
% 1.99/0.66  % (21064)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 1.99/0.66  fof(f238,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.99/0.66    inference(resolution,[],[f53,f29])).
% 1.99/0.66  fof(f56,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k6_subset_1(X1,k6_subset_1(X1,X2))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f46,f48])).
% 1.99/0.66  fof(f46,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f22])).
% 1.99/0.66  fof(f22,plain,(
% 1.99/0.66    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.99/0.66    inference(ennf_transformation,[],[f15])).
% 1.99/0.66  fof(f15,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.99/0.66  fof(f1264,plain,(
% 1.99/0.66    ( ! [X15] : (k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),X15)) = k3_subset_1(sK1,k6_subset_1(sK1,k6_subset_1(sK0,X15)))) )),
% 1.99/0.66    inference(forward_demodulation,[],[f1263,f238])).
% 1.99/0.66  fof(f1263,plain,(
% 1.99/0.66    ( ! [X15] : (k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),X15)) = k6_subset_1(sK1,k6_subset_1(sK1,k6_subset_1(sK0,X15)))) )),
% 1.99/0.66    inference(forward_demodulation,[],[f1173,f454])).
% 1.99/0.66  fof(f1173,plain,(
% 1.99/0.66    ( ! [X15] : (k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),X15)) = k6_subset_1(sK1,k6_subset_1(sK0,k2_xboole_0(k5_xboole_0(sK0,sK1),k6_subset_1(sK0,X15))))) )),
% 1.99/0.66    inference(superposition,[],[f60,f161])).
% 1.99/0.66  fof(f60,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k6_subset_1(X0,k2_xboole_0(X1,X2)) = k6_subset_1(k6_subset_1(X0,X1),k6_subset_1(X0,k2_xboole_0(X1,k6_subset_1(X0,X2))))) )),
% 1.99/0.66    inference(forward_demodulation,[],[f55,f54])).
% 1.99/0.66  fof(f55,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k6_subset_1(X0,k2_xboole_0(X1,X2)) = k6_subset_1(k6_subset_1(X0,X1),k6_subset_1(k6_subset_1(X0,X1),k6_subset_1(X0,X2)))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f45,f31,f48,f31,f31])).
% 1.99/0.66  fof(f45,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f7])).
% 1.99/0.66  fof(f7,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 1.99/0.66  % SZS output end Proof for theBenchmark
% 1.99/0.66  % (21031)------------------------------
% 1.99/0.66  % (21031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.66  % (21031)Termination reason: Refutation
% 1.99/0.66  
% 1.99/0.66  % (21031)Memory used [KB]: 7675
% 1.99/0.66  % (21031)Time elapsed: 0.228 s
% 1.99/0.66  % (21031)------------------------------
% 1.99/0.66  % (21031)------------------------------
% 1.99/0.66  % (21024)Success in time 0.296 s
%------------------------------------------------------------------------------
