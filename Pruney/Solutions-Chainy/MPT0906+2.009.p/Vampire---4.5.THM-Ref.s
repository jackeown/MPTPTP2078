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
% DateTime   : Thu Dec  3 12:59:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  41 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :   11
%              Number of atoms          :   63 ( 126 expanded)
%              Number of equality atoms :   54 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f27,f16])).

fof(f16,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f27,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f9,f25])).

fof(f25,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f23,f15])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f23,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f9,f22])).

fof(f22,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f21,f17])).

fof(f17,plain,
    ( sK2 != k1_mcart_1(sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f8,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_mcart_1(X2) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f8,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k1_xboole_0
       => ! [X2] :
            ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
           => ( k2_mcart_1(X2) != X2
              & k1_mcart_1(X2) != X2 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f21,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK2 = k1_mcart_1(sK2) ),
    inference(trivial_inequality_removal,[],[f20])).

fof(f20,plain,
    ( sK2 != sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK2 = k1_mcart_1(sK2) ),
    inference(superposition,[],[f18,f7])).

fof(f7,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f18,plain,
    ( sK2 != k2_mcart_1(sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f8,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k2_mcart_1(X2) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:28:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.44  % (9331)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (9331)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f27,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.46    inference(equality_resolution,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.21/0.46    inference(backward_demodulation,[],[f9,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    k1_xboole_0 = sK0),
% 0.21/0.46    inference(subsumption_resolution,[],[f23,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.46    inference(superposition,[],[f9,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.46    inference(subsumption_resolution,[],[f21,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    sK2 != k1_mcart_1(sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.46    inference(resolution,[],[f8,f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_mcart_1(X2) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : ((k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2) | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k2_zfmisc_1(X0,X1) != k1_xboole_0)),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.21/0.46    inference(negated_conjecture,[],[f3])).
% 0.21/0.46  fof(f3,conjecture,(
% 0.21/0.46    ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK2 = k1_mcart_1(sK2)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    sK2 != sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK2 = k1_mcart_1(sK2)),
% 0.21/0.46    inference(superposition,[],[f18,f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    sK2 != k2_mcart_1(sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.46    inference(resolution,[],[f8,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_mcart_1(X2) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (9331)------------------------------
% 0.21/0.46  % (9331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (9331)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (9331)Memory used [KB]: 1663
% 0.21/0.46  % (9331)Time elapsed: 0.033 s
% 0.21/0.46  % (9331)------------------------------
% 0.21/0.46  % (9331)------------------------------
% 0.21/0.46  % (9317)Success in time 0.099 s
%------------------------------------------------------------------------------
