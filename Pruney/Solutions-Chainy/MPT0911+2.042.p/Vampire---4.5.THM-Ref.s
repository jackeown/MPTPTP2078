%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:35 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 159 expanded)
%              Number of leaves         :    3 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 (1227 expanded)
%              Number of equality atoms :   91 ( 743 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f17,f16,f15,f14,f18,f50])).

fof(f50,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK4,k3_zfmisc_1(X6,X7,X8))
      | sK3 = k7_mcart_1(X6,X7,X8,sK4)
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | k1_xboole_0 = X8 ) ),
    inference(forward_demodulation,[],[f46,f42])).

fof(f42,plain,(
    sK3 = sK7(sK0,sK1,sK2,sK4) ),
    inference(unit_resulting_resolution,[],[f35,f32,f34,f33,f13])).

fof(f13,plain,(
    ! [X6,X7,X5] :
      ( k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f33,plain,(
    sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f16,f15,f17,f14,f23])).

% (30811)Refutation not found, incomplete strategy% (30811)------------------------------
% (30811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30811)Termination reason: Refutation not found, incomplete strategy

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f11])).

% (30811)Memory used [KB]: 10746
% (30811)Time elapsed: 0.126 s
% (30811)------------------------------
% (30811)------------------------------
fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f34,plain,(
    m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) ),
    inference(unit_resulting_resolution,[],[f15,f16,f17,f14,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) ),
    inference(unit_resulting_resolution,[],[f15,f16,f17,f14,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(unit_resulting_resolution,[],[f15,f16,f17,f14,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK4,k3_zfmisc_1(X6,X7,X8))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | k1_xboole_0 = X8
      | sK7(sK0,sK1,sK2,sK4) = k7_mcart_1(X6,X7,X8,sK4) ) ),
    inference(superposition,[],[f29,f33])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X6 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k3_mcart_1(X4,X5,X6) != X3
      | k7_mcart_1(X0,X1,X2,X3) = X6 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => ~ ( ? [X4,X5,X6] :
              ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                  & k6_mcart_1(X0,X1,X2,X3) = X5
                  & k5_mcart_1(X0,X1,X2,X3) = X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).

fof(f18,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:33:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.50  % (30812)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.51  % (30802)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.51  % (30812)Refutation not found, incomplete strategy% (30812)------------------------------
% 1.25/0.51  % (30812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.51  % (30812)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.51  
% 1.25/0.51  % (30812)Memory used [KB]: 10746
% 1.25/0.51  % (30812)Time elapsed: 0.108 s
% 1.25/0.51  % (30812)------------------------------
% 1.25/0.51  % (30812)------------------------------
% 1.25/0.52  % (30830)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.25/0.52  % (30811)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.52  % (30806)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.52  % (30828)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.52  % (30820)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.52  % (30817)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.52  % (30807)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.52  % (30806)Refutation found. Thanks to Tanya!
% 1.25/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.52  % SZS output start Proof for theBenchmark
% 1.25/0.52  fof(f87,plain,(
% 1.25/0.52    $false),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f17,f16,f15,f14,f18,f50])).
% 1.25/0.52  fof(f50,plain,(
% 1.25/0.52    ( ! [X6,X8,X7] : (~m1_subset_1(sK4,k3_zfmisc_1(X6,X7,X8)) | sK3 = k7_mcart_1(X6,X7,X8,sK4) | k1_xboole_0 = X6 | k1_xboole_0 = X7 | k1_xboole_0 = X8) )),
% 1.25/0.52    inference(forward_demodulation,[],[f46,f42])).
% 1.25/0.52  fof(f42,plain,(
% 1.25/0.52    sK3 = sK7(sK0,sK1,sK2,sK4)),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f35,f32,f34,f33,f13])).
% 1.25/0.52  fof(f13,plain,(
% 1.25/0.52    ( ! [X6,X7,X5] : (k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X7) )),
% 1.25/0.52    inference(cnf_transformation,[],[f8])).
% 1.25/0.52  fof(f8,plain,(
% 1.25/0.52    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.25/0.52    inference(flattening,[],[f7])).
% 1.25/0.52  fof(f7,plain,(
% 1.25/0.52    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.25/0.52    inference(ennf_transformation,[],[f6])).
% 1.25/0.52  fof(f6,negated_conjecture,(
% 1.25/0.52    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.25/0.52    inference(negated_conjecture,[],[f5])).
% 1.25/0.52  fof(f5,conjecture,(
% 1.25/0.52    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.25/0.52  fof(f33,plain,(
% 1.25/0.52    sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4))),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f16,f15,f17,f14,f23])).
% 1.25/0.52  % (30811)Refutation not found, incomplete strategy% (30811)------------------------------
% 1.25/0.52  % (30811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (30811)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  fof(f23,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3) )),
% 1.25/0.52    inference(cnf_transformation,[],[f11])).
% 1.25/0.52  % (30811)Memory used [KB]: 10746
% 1.25/0.52  % (30811)Time elapsed: 0.126 s
% 1.25/0.52  % (30811)------------------------------
% 1.25/0.52  % (30811)------------------------------
% 1.25/0.52  fof(f11,plain,(
% 1.25/0.52    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.25/0.52    inference(ennf_transformation,[],[f2])).
% 1.25/0.52  fof(f2,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).
% 1.25/0.52  fof(f34,plain,(
% 1.25/0.52    m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f15,f16,f17,f14,f24])).
% 1.25/0.52  fof(f24,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3),X1) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 1.25/0.52    inference(cnf_transformation,[],[f11])).
% 1.25/0.52  fof(f32,plain,(
% 1.25/0.52    m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f15,f16,f17,f14,f22])).
% 1.25/0.52  fof(f22,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),X2) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 1.25/0.52    inference(cnf_transformation,[],[f11])).
% 1.25/0.52  fof(f35,plain,(
% 1.25/0.52    m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 1.25/0.52    inference(unit_resulting_resolution,[],[f15,f16,f17,f14,f25])).
% 1.25/0.52  fof(f25,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X0) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 1.25/0.52    inference(cnf_transformation,[],[f11])).
% 1.25/0.52  fof(f46,plain,(
% 1.25/0.52    ( ! [X6,X8,X7] : (~m1_subset_1(sK4,k3_zfmisc_1(X6,X7,X8)) | k1_xboole_0 = X6 | k1_xboole_0 = X7 | k1_xboole_0 = X8 | sK7(sK0,sK1,sK2,sK4) = k7_mcart_1(X6,X7,X8,sK4)) )),
% 1.25/0.52    inference(superposition,[],[f29,f33])).
% 1.25/0.52  fof(f29,plain,(
% 1.25/0.52    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k7_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X6) )),
% 1.25/0.52    inference(equality_resolution,[],[f21])).
% 1.25/0.52  fof(f21,plain,(
% 1.25/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k3_mcart_1(X4,X5,X6) != X3 | k7_mcart_1(X0,X1,X2,X3) = X6) )),
% 1.25/0.52    inference(cnf_transformation,[],[f10])).
% 1.25/0.52  fof(f10,plain,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.25/0.52    inference(flattening,[],[f9])).
% 1.25/0.52  fof(f9,plain,(
% 1.25/0.52    ! [X0,X1,X2,X3] : ((! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.25/0.52    inference(ennf_transformation,[],[f4])).
% 1.25/0.52  fof(f4,axiom,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).
% 1.25/0.52  fof(f18,plain,(
% 1.25/0.52    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.25/0.52    inference(cnf_transformation,[],[f8])).
% 1.25/0.52  fof(f14,plain,(
% 1.25/0.52    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.25/0.52    inference(cnf_transformation,[],[f8])).
% 1.25/0.52  fof(f15,plain,(
% 1.25/0.52    k1_xboole_0 != sK0),
% 1.25/0.52    inference(cnf_transformation,[],[f8])).
% 1.25/0.52  fof(f16,plain,(
% 1.25/0.52    k1_xboole_0 != sK1),
% 1.25/0.52    inference(cnf_transformation,[],[f8])).
% 1.25/0.52  fof(f17,plain,(
% 1.25/0.52    k1_xboole_0 != sK2),
% 1.25/0.52    inference(cnf_transformation,[],[f8])).
% 1.25/0.52  % SZS output end Proof for theBenchmark
% 1.25/0.52  % (30806)------------------------------
% 1.25/0.52  % (30806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (30806)Termination reason: Refutation
% 1.25/0.52  
% 1.25/0.52  % (30806)Memory used [KB]: 6396
% 1.25/0.52  % (30806)Time elapsed: 0.125 s
% 1.25/0.52  % (30806)------------------------------
% 1.25/0.52  % (30806)------------------------------
% 1.25/0.52  % (30800)Success in time 0.179 s
%------------------------------------------------------------------------------
