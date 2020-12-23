%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  71 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :   12
%              Number of atoms          :   78 ( 331 expanded)
%              Number of equality atoms :   26 ( 126 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(subsumption_resolution,[],[f36,f13])).

fof(f13,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_relat_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ( k2_mcart_1(X1) = k2_mcart_1(X2)
                    & k1_mcart_1(X1) = k1_mcart_1(X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ( k2_mcart_1(X1) = k2_mcart_1(X2)
                  & k1_mcart_1(X1) = k1_mcart_1(X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_mcart_1)).

fof(f36,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f32,f35])).

fof(f35,plain,(
    sK1 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)) ),
    inference(subsumption_resolution,[],[f33,f16])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,
    ( ~ v1_relat_1(sK0)
    | sK1 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)) ),
    inference(resolution,[],[f27,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f27,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f25,f15])).

fof(f15,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f20,f14])).

fof(f14,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f32,plain,(
    sK2 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)) ),
    inference(forward_demodulation,[],[f31,f11])).

fof(f11,plain,(
    k1_mcart_1(sK1) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK1)) ),
    inference(forward_demodulation,[],[f30,f12])).

fof(f12,plain,(
    k2_mcart_1(sK1) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(subsumption_resolution,[],[f28,f16])).

fof(f28,plain,
    ( ~ v1_relat_1(sK0)
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(resolution,[],[f26,f21])).

fof(f26,plain,(
    r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f24,f15])).

fof(f24,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f20,f10])).

fof(f10,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (3553)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.42  % (3553)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f36,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    sK1 != sK2),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X1) = k2_mcart_1(X2) & k1_mcart_1(X1) = k1_mcart_1(X2) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) & v1_relat_1(X0) & ~v1_xboole_0(X0))),
% 0.21/0.42    inference(flattening,[],[f5])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (k2_mcart_1(X1) = k2_mcart_1(X2) & k1_mcart_1(X1) = k1_mcart_1(X2))) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) & (v1_relat_1(X0) & ~v1_xboole_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,negated_conjecture,(
% 0.21/0.42    ~! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ((k2_mcart_1(X1) = k2_mcart_1(X2) & k1_mcart_1(X1) = k1_mcart_1(X2)) => X1 = X2))))),
% 0.21/0.42    inference(negated_conjecture,[],[f3])).
% 0.21/0.42  fof(f3,conjecture,(
% 0.21/0.42    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ((k2_mcart_1(X1) = k2_mcart_1(X2) & k1_mcart_1(X1) = k1_mcart_1(X2)) => X1 = X2))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_mcart_1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    sK1 = sK2),
% 0.21/0.42    inference(backward_demodulation,[],[f32,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    sK1 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1))),
% 0.21/0.42    inference(subsumption_resolution,[],[f33,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ~v1_relat_1(sK0) | sK1 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1))),
% 0.21/0.42    inference(resolution,[],[f27,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    r2_hidden(sK1,sK0)),
% 0.21/0.42    inference(subsumption_resolution,[],[f25,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ~v1_xboole_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    r2_hidden(sK1,sK0) | v1_xboole_0(sK0)),
% 0.21/0.42    inference(resolution,[],[f20,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    m1_subset_1(sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    sK2 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1))),
% 0.21/0.42    inference(forward_demodulation,[],[f31,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    k1_mcart_1(sK1) = k1_mcart_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK1))),
% 0.21/0.42    inference(forward_demodulation,[],[f30,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    k2_mcart_1(sK1) = k2_mcart_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.42    inference(subsumption_resolution,[],[f28,f16])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ~v1_relat_1(sK0) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.42    inference(resolution,[],[f26,f21])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    r2_hidden(sK2,sK0)),
% 0.21/0.42    inference(subsumption_resolution,[],[f24,f15])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 0.21/0.42    inference(resolution,[],[f20,f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    m1_subset_1(sK2,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (3553)------------------------------
% 0.21/0.42  % (3553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (3553)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (3553)Memory used [KB]: 1663
% 0.21/0.42  % (3553)Time elapsed: 0.004 s
% 0.21/0.42  % (3553)------------------------------
% 0.21/0.42  % (3553)------------------------------
% 0.21/0.42  % (3535)Success in time 0.068 s
%------------------------------------------------------------------------------
