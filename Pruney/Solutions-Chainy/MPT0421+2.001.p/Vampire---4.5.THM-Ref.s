%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   16 (  31 expanded)
%              Number of leaves         :    2 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  85 expanded)
%              Number of equality atoms :   17 (  44 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15,f9])).

fof(f9,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_setfam_1)).

fof(f15,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f13,f14])).

fof(f14,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f10,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f10,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,plain,(
    sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f12,f8])).

fof(f8,plain,(
    k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,plain,(
    sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) ),
    inference(resolution,[],[f7,f11])).

fof(f7,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:38:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (31462)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.46  % (31457)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.46  % (31457)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(subsumption_resolution,[],[f15,f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    sK1 != sK2),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,plain,(
% 0.22/0.46    ? [X0,X1] : (? [X2] : (X1 != X2 & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.46    inference(flattening,[],[f4])).
% 0.22/0.46  fof(f4,plain,(
% 0.22/0.46    ? [X0,X1] : (? [X2] : ((X1 != X2 & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2) => X1 = X2)))),
% 0.22/0.46    inference(negated_conjecture,[],[f2])).
% 0.22/0.46  fof(f2,conjecture,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2) => X1 = X2)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_setfam_1)).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    sK1 = sK2),
% 0.22/0.46    inference(backward_demodulation,[],[f13,f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 0.22/0.46    inference(resolution,[],[f10,f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.22/0.46    inference(cnf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,plain,(
% 0.22/0.46    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.46    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 0.22/0.46    inference(forward_demodulation,[],[f12,f8])).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK2))),
% 0.22/0.46    inference(resolution,[],[f7,f11])).
% 0.22/0.46  fof(f7,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (31457)------------------------------
% 0.22/0.46  % (31457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (31457)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (31457)Memory used [KB]: 1535
% 0.22/0.46  % (31457)Time elapsed: 0.057 s
% 0.22/0.46  % (31457)------------------------------
% 0.22/0.46  % (31457)------------------------------
% 0.22/0.47  % (31443)Success in time 0.106 s
%------------------------------------------------------------------------------
