%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 209 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(subsumption_resolution,[],[f121,f109])).

fof(f109,plain,(
    ~ r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f85,f90])).

fof(f90,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f73,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
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

fof(f73,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f70,f26])).

fof(f26,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f70,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

fof(f85,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f60,plain,(
    ~ r1_tarski(sK1,k4_xboole_0(sK0,sK3)) ),
    inference(backward_demodulation,[],[f23,f55])).

fof(f55,plain,(
    k3_subset_1(sK0,sK3) = k4_xboole_0(sK0,sK3) ),
    inference(resolution,[],[f20,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f121,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f117,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f117,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f97,f22])).

fof(f22,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | r1_xboole_0(X0,sK1) ) ),
    inference(superposition,[],[f38,f46])).

fof(f46,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f21,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f21,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:22:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.40  % (21789)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.41  % (21789)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f122,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(subsumption_resolution,[],[f121,f109])).
% 0.20/0.41  fof(f109,plain,(
% 0.20/0.41    ~r1_xboole_0(sK1,sK3)),
% 0.20/0.41    inference(resolution,[],[f85,f90])).
% 0.20/0.41  fof(f90,plain,(
% 0.20/0.41    r1_tarski(sK1,sK0)),
% 0.20/0.41    inference(resolution,[],[f73,f42])).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(equality_resolution,[],[f35])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.41  fof(f73,plain,(
% 0.20/0.41    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.41    inference(subsumption_resolution,[],[f70,f26])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,axiom,(
% 0.20/0.41    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.41  fof(f70,plain,(
% 0.20/0.41    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.41    inference(resolution,[],[f25,f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(flattening,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(X1,k3_subset_1(X0,X3)) & (r1_xboole_0(X3,X2) & r1_tarski(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.20/0.41    inference(negated_conjecture,[],[f9])).
% 0.20/0.41  fof(f9,conjecture,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).
% 0.20/0.41  fof(f85,plain,(
% 0.20/0.41    ~r1_tarski(sK1,sK0) | ~r1_xboole_0(sK1,sK3)),
% 0.20/0.41    inference(resolution,[],[f60,f41])).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.41    inference(flattening,[],[f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.20/0.41  fof(f60,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k4_xboole_0(sK0,sK3))),
% 0.20/0.41    inference(backward_demodulation,[],[f23,f55])).
% 0.20/0.41  fof(f55,plain,(
% 0.20/0.41    k3_subset_1(sK0,sK3) = k4_xboole_0(sK0,sK3)),
% 0.20/0.41    inference(resolution,[],[f20,f33])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,axiom,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f121,plain,(
% 0.20/0.41    r1_xboole_0(sK1,sK3)),
% 0.20/0.41    inference(resolution,[],[f117,f32])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.41  fof(f117,plain,(
% 0.20/0.41    r1_xboole_0(sK3,sK1)),
% 0.20/0.41    inference(resolution,[],[f97,f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    r1_xboole_0(sK3,sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f97,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_xboole_0(X0,sK2) | r1_xboole_0(X0,sK1)) )),
% 0.20/0.41    inference(superposition,[],[f38,f46])).
% 0.20/0.41  fof(f46,plain,(
% 0.20/0.41    sK2 = k2_xboole_0(sK1,sK2)),
% 0.20/0.41    inference(resolution,[],[f21,f31])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    r1_tarski(sK1,sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (21789)------------------------------
% 0.20/0.41  % (21789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (21789)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (21789)Memory used [KB]: 1663
% 0.20/0.41  % (21789)Time elapsed: 0.005 s
% 0.20/0.41  % (21789)------------------------------
% 0.20/0.41  % (21789)------------------------------
% 0.20/0.41  % (21775)Success in time 0.057 s
%------------------------------------------------------------------------------
