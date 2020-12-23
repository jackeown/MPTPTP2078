%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:15 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 235 expanded)
%              Number of leaves         :   11 (  51 expanded)
%              Depth                    :   20
%              Number of atoms          :  103 ( 629 expanded)
%              Number of equality atoms :   49 ( 189 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f207])).

fof(f207,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f28,f172])).

fof(f172,plain,(
    sK1 = k3_subset_1(sK0,sK2) ),
    inference(backward_demodulation,[],[f67,f170])).

fof(f170,plain,(
    sK2 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f169,f77])).

fof(f77,plain,(
    sK2 = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f40,f58])).

fof(f58,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f42,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f42,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f26,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f26,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f169,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f168,f118])).

fof(f118,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f81,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f81,plain,(
    k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f68,f34])).

fof(f68,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f53,f62])).

fof(f62,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f29,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f27,f47])).

fof(f47,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f25,f31])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f168,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f164,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f164,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f158,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f158,plain,(
    r1_tarski(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f157,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f157,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f152,f58])).

fof(f152,plain,(
    k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f116,f103])).

fof(f103,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f97,f67])).

fof(f97,plain,(
    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f69,f31])).

fof(f69,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f61,f62])).

fof(f61,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f116,plain,(
    ! [X2] : k3_xboole_0(sK2,k4_xboole_0(sK0,X2)) = k4_xboole_0(sK2,X2) ),
    inference(forward_demodulation,[],[f115,f113])).

fof(f113,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f37,f91])).

fof(f91,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f85,f52])).

fof(f52,plain,(
    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f48,f47])).

fof(f48,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f85,plain,(
    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f54,f31])).

fof(f54,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f46,f47])).

fof(f46,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f32])).

fof(f115,plain,(
    ! [X2] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X2)) = k3_xboole_0(sK2,k4_xboole_0(sK0,X2)) ),
    inference(superposition,[],[f36,f91])).

fof(f67,plain,(
    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f63,f62])).

fof(f63,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f29,f30])).

fof(f28,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (807305216)
% 0.14/0.36  ipcrm: permission denied for id (807337985)
% 0.14/0.37  ipcrm: permission denied for id (807436294)
% 0.14/0.37  ipcrm: permission denied for id (807501833)
% 0.14/0.38  ipcrm: permission denied for id (807600141)
% 0.14/0.38  ipcrm: permission denied for id (807632910)
% 0.14/0.38  ipcrm: permission denied for id (807698448)
% 0.21/0.39  ipcrm: permission denied for id (807895070)
% 0.21/0.40  ipcrm: permission denied for id (807960609)
% 0.21/0.40  ipcrm: permission denied for id (808058917)
% 0.21/0.40  ipcrm: permission denied for id (808124456)
% 0.21/0.40  ipcrm: permission denied for id (808157225)
% 0.21/0.41  ipcrm: permission denied for id (808189995)
% 0.21/0.42  ipcrm: permission denied for id (808288309)
% 0.21/0.42  ipcrm: permission denied for id (808386617)
% 0.21/0.42  ipcrm: permission denied for id (808452155)
% 0.21/0.43  ipcrm: permission denied for id (808484924)
% 0.21/0.43  ipcrm: permission denied for id (808517695)
% 0.21/0.43  ipcrm: permission denied for id (808583233)
% 0.21/0.43  ipcrm: permission denied for id (808616002)
% 0.21/0.44  ipcrm: permission denied for id (808648776)
% 0.21/0.44  ipcrm: permission denied for id (808714315)
% 0.21/0.44  ipcrm: permission denied for id (808747084)
% 0.21/0.45  ipcrm: permission denied for id (808812624)
% 0.21/0.45  ipcrm: permission denied for id (808845394)
% 0.21/0.45  ipcrm: permission denied for id (808910932)
% 0.21/0.45  ipcrm: permission denied for id (808943701)
% 0.21/0.45  ipcrm: permission denied for id (808976470)
% 0.21/0.46  ipcrm: permission denied for id (809074779)
% 0.21/0.46  ipcrm: permission denied for id (809140318)
% 0.21/0.47  ipcrm: permission denied for id (809205857)
% 0.21/0.47  ipcrm: permission denied for id (809238628)
% 0.21/0.48  ipcrm: permission denied for id (809468014)
% 0.21/0.48  ipcrm: permission denied for id (809533552)
% 0.21/0.48  ipcrm: permission denied for id (809566321)
% 0.21/0.49  ipcrm: permission denied for id (809599090)
% 0.21/0.49  ipcrm: permission denied for id (809631859)
% 0.21/0.49  ipcrm: permission denied for id (809664628)
% 0.21/0.49  ipcrm: permission denied for id (809730167)
% 0.21/0.49  ipcrm: permission denied for id (809762936)
% 0.21/0.50  ipcrm: permission denied for id (809861244)
% 0.21/0.50  ipcrm: permission denied for id (809894014)
% 0.36/0.63  % (23709)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.36/0.63  % (23716)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.36/0.64  % (23734)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.36/0.65  % (23725)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.36/0.65  % (23711)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.36/0.66  % (23718)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.36/0.66  % (23707)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.36/0.67  % (23714)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.36/0.67  % (23708)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.36/0.67  % (23726)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.36/0.67  % (23711)Refutation found. Thanks to Tanya!
% 0.36/0.67  % SZS status Theorem for theBenchmark
% 0.36/0.67  % SZS output start Proof for theBenchmark
% 0.36/0.67  fof(f208,plain,(
% 0.36/0.67    $false),
% 0.36/0.67    inference(trivial_inequality_removal,[],[f207])).
% 0.36/0.67  fof(f207,plain,(
% 0.36/0.67    sK1 != sK1),
% 0.36/0.67    inference(superposition,[],[f28,f172])).
% 0.36/0.67  fof(f172,plain,(
% 0.36/0.67    sK1 = k3_subset_1(sK0,sK2)),
% 0.36/0.67    inference(backward_demodulation,[],[f67,f170])).
% 0.36/0.67  fof(f170,plain,(
% 0.36/0.67    sK2 = k4_xboole_0(sK0,sK1)),
% 0.36/0.67    inference(forward_demodulation,[],[f169,f77])).
% 0.36/0.67  fof(f77,plain,(
% 0.36/0.67    sK2 = k2_xboole_0(sK2,k1_xboole_0)),
% 0.36/0.67    inference(superposition,[],[f40,f58])).
% 0.36/0.67  fof(f58,plain,(
% 0.36/0.67    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f42,f34])).
% 0.36/0.67  fof(f34,plain,(
% 0.36/0.67    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.36/0.67    inference(cnf_transformation,[],[f1])).
% 0.36/0.67  fof(f1,axiom,(
% 0.36/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.36/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.36/0.67  fof(f42,plain,(
% 0.36/0.67    r1_xboole_0(sK2,sK1)),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f26,f35])).
% 0.36/0.67  fof(f35,plain,(
% 0.36/0.67    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.36/0.67    inference(cnf_transformation,[],[f23])).
% 0.36/0.67  fof(f23,plain,(
% 0.36/0.67    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.36/0.67    inference(ennf_transformation,[],[f2])).
% 0.36/0.67  fof(f2,axiom,(
% 0.36/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.36/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.36/0.67  fof(f26,plain,(
% 0.36/0.67    r1_xboole_0(sK1,sK2)),
% 0.36/0.67    inference(cnf_transformation,[],[f19])).
% 0.36/0.67  fof(f19,plain,(
% 0.36/0.67    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.36/0.67    inference(flattening,[],[f18])).
% 0.36/0.67  fof(f18,plain,(
% 0.36/0.67    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & (r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.36/0.67    inference(ennf_transformation,[],[f17])).
% 0.36/0.67  fof(f17,negated_conjecture,(
% 0.36/0.67    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 0.36/0.67    inference(negated_conjecture,[],[f16])).
% 0.36/0.67  fof(f16,conjecture,(
% 0.36/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 0.36/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).
% 0.36/0.67  fof(f40,plain,(
% 0.36/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.36/0.67    inference(cnf_transformation,[],[f3])).
% 0.36/0.67  fof(f3,axiom,(
% 0.36/0.67    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.36/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.36/0.67  fof(f169,plain,(
% 0.36/0.67    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 0.36/0.67    inference(forward_demodulation,[],[f168,f118])).
% 0.36/0.67  fof(f118,plain,(
% 0.36/0.67    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.36/0.67    inference(superposition,[],[f81,f36])).
% 0.36/0.67  fof(f36,plain,(
% 0.36/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.36/0.67    inference(cnf_transformation,[],[f7])).
% 0.36/0.67  fof(f7,axiom,(
% 0.36/0.67    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.36/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).
% 0.36/0.67  fof(f81,plain,(
% 0.36/0.67    k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f68,f34])).
% 0.36/0.67  fof(f68,plain,(
% 0.36/0.67    r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.36/0.67    inference(backward_demodulation,[],[f53,f62])).
% 0.36/0.67  fof(f62,plain,(
% 0.36/0.67    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f29,f31])).
% 0.36/0.67  fof(f31,plain,(
% 0.36/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.36/0.67    inference(cnf_transformation,[],[f21])).
% 0.36/0.67  fof(f21,plain,(
% 0.36/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.36/0.67    inference(ennf_transformation,[],[f13])).
% 0.36/0.67  fof(f13,axiom,(
% 0.36/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.36/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.36/0.67  fof(f29,plain,(
% 0.36/0.67    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.36/0.67    inference(cnf_transformation,[],[f19])).
% 0.36/0.67  fof(f53,plain,(
% 0.36/0.67    r1_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.36/0.67    inference(backward_demodulation,[],[f27,f47])).
% 0.36/0.67  fof(f47,plain,(
% 0.36/0.67    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f25,f31])).
% 0.36/0.67  fof(f25,plain,(
% 0.36/0.67    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.36/0.67    inference(cnf_transformation,[],[f19])).
% 0.36/0.67  fof(f27,plain,(
% 0.36/0.67    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))),
% 0.36/0.67    inference(cnf_transformation,[],[f19])).
% 0.36/0.67  fof(f168,plain,(
% 0.36/0.67    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.36/0.67    inference(forward_demodulation,[],[f164,f37])).
% 0.36/0.67  fof(f37,plain,(
% 0.36/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.36/0.67    inference(cnf_transformation,[],[f5])).
% 0.36/0.67  fof(f5,axiom,(
% 0.36/0.67    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.36/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.36/0.67  fof(f164,plain,(
% 0.36/0.67    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK0,sK1),sK2))),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f158,f41])).
% 0.36/0.67  fof(f41,plain,(
% 0.36/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.36/0.67    inference(cnf_transformation,[],[f24])).
% 0.36/0.67  fof(f24,plain,(
% 0.36/0.67    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.36/0.67    inference(ennf_transformation,[],[f6])).
% 0.36/0.67  fof(f6,axiom,(
% 0.36/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.36/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.36/0.67  fof(f158,plain,(
% 0.36/0.67    r1_tarski(sK2,k4_xboole_0(sK0,sK1))),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f157,f39])).
% 0.36/0.67  fof(f39,plain,(
% 0.36/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.36/0.67    inference(cnf_transformation,[],[f4])).
% 0.36/0.67  fof(f4,axiom,(
% 0.36/0.67    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.36/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.36/0.67  fof(f157,plain,(
% 0.36/0.67    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 0.36/0.67    inference(forward_demodulation,[],[f152,f58])).
% 0.36/0.67  fof(f152,plain,(
% 0.36/0.67    k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 0.36/0.67    inference(superposition,[],[f116,f103])).
% 0.36/0.67  fof(f103,plain,(
% 0.36/0.67    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.36/0.67    inference(forward_demodulation,[],[f97,f67])).
% 0.36/0.67  fof(f97,plain,(
% 0.36/0.67    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f69,f31])).
% 0.36/0.67  fof(f69,plain,(
% 0.36/0.67    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.36/0.67    inference(forward_demodulation,[],[f61,f62])).
% 0.36/0.67  fof(f61,plain,(
% 0.36/0.67    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f29,f32])).
% 0.36/0.67  fof(f32,plain,(
% 0.36/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.36/0.67    inference(cnf_transformation,[],[f22])).
% 0.36/0.67  fof(f22,plain,(
% 0.36/0.67    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.36/0.67    inference(ennf_transformation,[],[f14])).
% 0.36/0.67  fof(f14,axiom,(
% 0.36/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.36/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.36/0.67  fof(f116,plain,(
% 0.36/0.67    ( ! [X2] : (k3_xboole_0(sK2,k4_xboole_0(sK0,X2)) = k4_xboole_0(sK2,X2)) )),
% 0.36/0.67    inference(forward_demodulation,[],[f115,f113])).
% 0.36/0.67  fof(f113,plain,(
% 0.36/0.67    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(sK2,X0)) )),
% 0.36/0.67    inference(superposition,[],[f37,f91])).
% 0.36/0.67  fof(f91,plain,(
% 0.36/0.67    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.36/0.67    inference(forward_demodulation,[],[f85,f52])).
% 0.36/0.67  fof(f52,plain,(
% 0.36/0.67    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 0.36/0.67    inference(backward_demodulation,[],[f48,f47])).
% 0.36/0.67  fof(f48,plain,(
% 0.36/0.67    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f25,f30])).
% 0.36/0.67  fof(f30,plain,(
% 0.36/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.36/0.67    inference(cnf_transformation,[],[f20])).
% 0.36/0.67  fof(f20,plain,(
% 0.36/0.67    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.36/0.67    inference(ennf_transformation,[],[f15])).
% 0.36/0.67  fof(f15,axiom,(
% 0.36/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.36/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.36/0.67  fof(f85,plain,(
% 0.36/0.67    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f54,f31])).
% 0.36/0.67  fof(f54,plain,(
% 0.36/0.67    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.36/0.67    inference(forward_demodulation,[],[f46,f47])).
% 0.36/0.67  fof(f46,plain,(
% 0.36/0.67    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f25,f32])).
% 0.36/0.67  fof(f115,plain,(
% 0.36/0.67    ( ! [X2] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X2)) = k3_xboole_0(sK2,k4_xboole_0(sK0,X2))) )),
% 0.36/0.67    inference(superposition,[],[f36,f91])).
% 0.36/0.67  fof(f67,plain,(
% 0.36/0.67    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.36/0.67    inference(backward_demodulation,[],[f63,f62])).
% 0.36/0.67  fof(f63,plain,(
% 0.36/0.67    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.36/0.67    inference(unit_resulting_resolution,[],[f29,f30])).
% 0.36/0.67  fof(f28,plain,(
% 0.36/0.67    sK1 != k3_subset_1(sK0,sK2)),
% 0.36/0.67    inference(cnf_transformation,[],[f19])).
% 0.36/0.67  % SZS output end Proof for theBenchmark
% 0.36/0.67  % (23711)------------------------------
% 0.36/0.67  % (23711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.67  % (23711)Termination reason: Refutation
% 0.36/0.67  
% 0.36/0.67  % (23711)Memory used [KB]: 6268
% 0.36/0.67  % (23711)Time elapsed: 0.116 s
% 0.36/0.67  % (23711)------------------------------
% 0.36/0.67  % (23711)------------------------------
% 0.36/0.68  % (23573)Success in time 0.319 s
%------------------------------------------------------------------------------
