%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:59 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 137 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 427 expanded)
%              Number of equality atoms :   48 ( 125 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f92,f61])).

fof(f61,plain,(
    sK1 = k1_tarski(sK3(sK1)) ),
    inference(forward_demodulation,[],[f60,f48])).

fof(f48,plain,(
    sK1 = k6_domain_1(sK1,sK3(sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f23,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK3(X0)) = X0
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f23,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f22,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f47,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f47,plain,(
    m1_subset_1(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f22,f23,f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) != sK1 ),
    inference(forward_demodulation,[],[f90,f75])).

fof(f75,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f72,f40])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f72,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f41,f53])).

fof(f53,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f24,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) != k2_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f25,f79,f88,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f88,plain,(
    k1_xboole_0 != sK0 ),
    inference(superposition,[],[f39,f62])).

fof(f62,plain,(
    sK0 = k2_xboole_0(k1_tarski(sK4(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f49,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f49,plain,(
    r2_hidden(sK4(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f26,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f79,plain,(
    k1_xboole_0 != sK1 ),
    inference(superposition,[],[f76,f75])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 != k2_xboole_0(sK1,X0) ),
    inference(superposition,[],[f39,f61])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.55/0.56  % (6846)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.55/0.57  % (6847)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.55/0.58  % (6846)Refutation found. Thanks to Tanya!
% 1.55/0.58  % SZS status Theorem for theBenchmark
% 1.55/0.58  % SZS output start Proof for theBenchmark
% 1.55/0.58  fof(f105,plain,(
% 1.55/0.58    $false),
% 1.55/0.58    inference(trivial_inequality_removal,[],[f104])).
% 1.55/0.58  fof(f104,plain,(
% 1.55/0.58    sK1 != sK1),
% 1.55/0.58    inference(superposition,[],[f92,f61])).
% 1.55/0.58  fof(f61,plain,(
% 1.55/0.58    sK1 = k1_tarski(sK3(sK1))),
% 1.55/0.58    inference(forward_demodulation,[],[f60,f48])).
% 1.55/0.58  fof(f48,plain,(
% 1.55/0.58    sK1 = k6_domain_1(sK1,sK3(sK1))),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f22,f23,f33])).
% 1.55/0.58  fof(f33,plain,(
% 1.55/0.58    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = X0 | ~v1_zfmisc_1(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f17])).
% 1.55/0.58  fof(f17,plain,(
% 1.55/0.58    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f11])).
% 1.55/0.58  fof(f11,axiom,(
% 1.55/0.58    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 1.55/0.58  fof(f23,plain,(
% 1.55/0.58    v1_zfmisc_1(sK1)),
% 1.55/0.58    inference(cnf_transformation,[],[f15])).
% 1.55/0.58  fof(f15,plain,(
% 1.55/0.58    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.55/0.58    inference(flattening,[],[f14])).
% 1.55/0.58  fof(f14,plain,(
% 1.55/0.58    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f13])).
% 1.55/0.58  fof(f13,negated_conjecture,(
% 1.55/0.58    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.55/0.58    inference(negated_conjecture,[],[f12])).
% 1.55/0.58  fof(f12,conjecture,(
% 1.55/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.55/0.58  fof(f22,plain,(
% 1.55/0.58    ~v1_xboole_0(sK1)),
% 1.55/0.58    inference(cnf_transformation,[],[f15])).
% 1.55/0.58  fof(f60,plain,(
% 1.55/0.58    k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1))),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f22,f47,f35])).
% 1.55/0.58  fof(f35,plain,(
% 1.55/0.58    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f19])).
% 1.55/0.58  fof(f19,plain,(
% 1.55/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.55/0.58    inference(flattening,[],[f18])).
% 1.55/0.58  fof(f18,plain,(
% 1.55/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f10])).
% 1.55/0.58  fof(f10,axiom,(
% 1.55/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.55/0.58  fof(f47,plain,(
% 1.55/0.58    m1_subset_1(sK3(sK1),sK1)),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f22,f23,f32])).
% 1.55/0.58  fof(f32,plain,(
% 1.55/0.58    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f17])).
% 1.55/0.58  fof(f92,plain,(
% 1.55/0.58    ( ! [X0] : (k1_tarski(X0) != sK1) )),
% 1.55/0.58    inference(forward_demodulation,[],[f90,f75])).
% 1.55/0.58  fof(f75,plain,(
% 1.55/0.58    sK1 = k2_xboole_0(sK1,sK0)),
% 1.55/0.58    inference(forward_demodulation,[],[f72,f40])).
% 1.55/0.58  fof(f40,plain,(
% 1.55/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.58    inference(cnf_transformation,[],[f4])).
% 1.55/0.58  fof(f4,axiom,(
% 1.55/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.55/0.58  fof(f72,plain,(
% 1.55/0.58    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 1.55/0.58    inference(superposition,[],[f41,f53])).
% 1.55/0.58  fof(f53,plain,(
% 1.55/0.58    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f24,f27])).
% 1.55/0.58  fof(f27,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.55/0.58    inference(cnf_transformation,[],[f3])).
% 1.55/0.58  fof(f3,axiom,(
% 1.55/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.55/0.58  fof(f24,plain,(
% 1.55/0.58    r1_tarski(sK0,sK1)),
% 1.55/0.58    inference(cnf_transformation,[],[f15])).
% 1.55/0.58  fof(f41,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f5])).
% 1.55/0.58  fof(f5,axiom,(
% 1.55/0.58    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.55/0.58  fof(f90,plain,(
% 1.55/0.58    ( ! [X0] : (k1_tarski(X0) != k2_xboole_0(sK1,sK0)) )),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f25,f79,f88,f38])).
% 1.55/0.58  fof(f38,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | X1 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 1.55/0.58    inference(cnf_transformation,[],[f20])).
% 1.55/0.58  fof(f20,plain,(
% 1.55/0.58    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 1.55/0.58    inference(ennf_transformation,[],[f8])).
% 1.55/0.58  fof(f8,axiom,(
% 1.55/0.58    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.55/0.58  fof(f88,plain,(
% 1.55/0.58    k1_xboole_0 != sK0),
% 1.55/0.58    inference(superposition,[],[f39,f62])).
% 1.55/0.58  fof(f62,plain,(
% 1.55/0.58    sK0 = k2_xboole_0(k1_tarski(sK4(sK0)),sK0)),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f49,f42])).
% 1.55/0.58  fof(f42,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 1.55/0.58    inference(cnf_transformation,[],[f21])).
% 1.55/0.58  fof(f21,plain,(
% 1.55/0.58    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.55/0.58    inference(ennf_transformation,[],[f6])).
% 1.55/0.58  fof(f6,axiom,(
% 1.55/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 1.55/0.58  fof(f49,plain,(
% 1.55/0.58    r2_hidden(sK4(sK0),sK0)),
% 1.55/0.58    inference(unit_resulting_resolution,[],[f26,f36])).
% 1.55/0.58  fof(f36,plain,(
% 1.55/0.58    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f1])).
% 1.55/0.58  fof(f1,axiom,(
% 1.55/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.55/0.58  fof(f26,plain,(
% 1.55/0.58    ~v1_xboole_0(sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f15])).
% 1.55/0.58  fof(f39,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f9])).
% 1.55/0.58  fof(f9,axiom,(
% 1.55/0.58    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.55/0.58  fof(f79,plain,(
% 1.55/0.58    k1_xboole_0 != sK1),
% 1.55/0.58    inference(superposition,[],[f76,f75])).
% 1.55/0.58  fof(f76,plain,(
% 1.55/0.58    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(sK1,X0)) )),
% 1.55/0.58    inference(superposition,[],[f39,f61])).
% 1.55/0.58  fof(f25,plain,(
% 1.55/0.58    sK0 != sK1),
% 1.55/0.58    inference(cnf_transformation,[],[f15])).
% 1.55/0.58  % SZS output end Proof for theBenchmark
% 1.55/0.58  % (6846)------------------------------
% 1.55/0.58  % (6846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (6846)Termination reason: Refutation
% 1.55/0.58  
% 1.55/0.58  % (6846)Memory used [KB]: 6268
% 1.55/0.58  % (6846)Time elapsed: 0.166 s
% 1.55/0.58  % (6846)------------------------------
% 1.55/0.58  % (6846)------------------------------
% 1.55/0.58  % (6840)Success in time 0.221 s
%------------------------------------------------------------------------------
