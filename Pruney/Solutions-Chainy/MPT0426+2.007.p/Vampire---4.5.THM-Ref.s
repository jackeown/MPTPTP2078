%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 458 expanded)
%              Number of leaves         :    6 (  84 expanded)
%              Depth                    :   20
%              Number of atoms          :  163 (1865 expanded)
%              Number of equality atoms :   67 ( 537 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(subsumption_resolution,[],[f166,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f166,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK3),k1_xboole_0) ),
    inference(resolution,[],[f163,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f163,plain,(
    r2_hidden(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f161,f18])).

fof(f18,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

fof(f161,plain,
    ( ~ r2_hidden(sK1,sK0)
    | r2_hidden(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f140,f147])).

fof(f147,plain,(
    sK0 = k8_setfam_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f129,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f129,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(backward_demodulation,[],[f17,f125])).

fof(f125,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f124,f82])).

fof(f82,plain,
    ( ~ r2_hidden(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f75,f51])).

fof(f51,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ r2_hidden(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f15,f45])).

fof(f45,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f43,f44])).

fof(f44,plain,(
    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f17,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f43,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f17,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f74,f15])).

fof(f74,plain,
    ( r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | k1_xboole_0 = sK2
    | r2_hidden(sK1,k1_setfam_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,
    ( r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | k1_xboole_0 = sK2
    | r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | r2_hidden(sK1,k1_setfam_1(sK2)) ),
    inference(resolution,[],[f62,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X2,sK5(X0,X2))
      | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X2,sK5(X0,X2))
      | r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f62,plain,(
    ! [X6] :
      ( r2_hidden(sK1,sK5(sK2,X6))
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2))
      | k1_xboole_0 = sK2
      | r2_hidden(X6,k1_setfam_1(sK2)) ) ),
    inference(resolution,[],[f16,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X2),X0)
      | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X2),X0)
      | r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(sK1,X3)
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f124,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f99,f83])).

fof(f83,plain,
    ( r2_hidden(sK3,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f76,f52])).

fof(f52,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | r2_hidden(sK3,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f14,f45])).

fof(f14,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f76,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK1,k1_setfam_1(sK2))
    | r2_hidden(sK3,sK2) ),
    inference(resolution,[],[f74,f14])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_xboole_0 = sK2
      | r2_hidden(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK2
      | ~ r2_hidden(X0,sK2)
      | r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f81,f38])).

% (22265)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f38,plain,(
    ! [X2,X0,X3] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f74,f45])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f140,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | r2_hidden(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f126,f125])).

fof(f126,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f14,f125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:29:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (22272)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (22272)Refutation not found, incomplete strategy% (22272)------------------------------
% 0.20/0.46  % (22272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22277)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.47  % (22272)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (22272)Memory used [KB]: 6012
% 0.20/0.47  % (22272)Time elapsed: 0.059 s
% 0.20/0.47  % (22272)------------------------------
% 0.20/0.47  % (22272)------------------------------
% 0.20/0.48  % (22261)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (22274)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (22263)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (22273)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (22266)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (22273)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f166,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    k1_xboole_0 = k2_xboole_0(k1_tarski(sK3),k1_xboole_0)),
% 0.20/0.49    inference(resolution,[],[f163,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    r2_hidden(sK3,k1_xboole_0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f161,f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    r2_hidden(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f6])).
% 0.20/0.49  fof(f6,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    ~r2_hidden(sK1,sK0) | r2_hidden(sK3,k1_xboole_0)),
% 0.20/0.49    inference(backward_demodulation,[],[f140,f147])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    sK0 = k8_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.49    inference(resolution,[],[f129,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(equality_resolution,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.49    inference(backward_demodulation,[],[f17,f125])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    k1_xboole_0 = sK2),
% 0.20/0.49    inference(subsumption_resolution,[],[f124,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ~r2_hidden(sK1,sK3) | k1_xboole_0 = sK2),
% 0.20/0.49    inference(subsumption_resolution,[],[f75,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k1_setfam_1(sK2)) | ~r2_hidden(sK1,sK3) | k1_xboole_0 = sK2),
% 0.20/0.49    inference(superposition,[],[f15,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 0.20/0.49    inference(backward_demodulation,[],[f43,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.49    inference(resolution,[],[f17,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 0.20/0.49    inference(resolution,[],[f17,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | ~r2_hidden(sK1,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | r2_hidden(sK1,k1_setfam_1(sK2)) | ~r2_hidden(sK1,sK3)),
% 0.20/0.49    inference(resolution,[],[f74,f15])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | k1_xboole_0 = sK2 | r2_hidden(sK1,k1_setfam_1(sK2))),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | k1_xboole_0 = sK2 | r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | r2_hidden(sK1,k1_setfam_1(sK2))),
% 0.20/0.49    inference(resolution,[],[f62,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X2,X0] : (k1_xboole_0 = X0 | ~r2_hidden(X2,sK5(X0,X2)) | r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.20/0.49    inference(equality_resolution,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X2,sK5(X0,X2)) | r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X6] : (r2_hidden(sK1,sK5(sK2,X6)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | k1_xboole_0 = sK2 | r2_hidden(X6,k1_setfam_1(sK2))) )),
% 0.20/0.49    inference(resolution,[],[f16,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0,X2),X0) | r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.20/0.49    inference(equality_resolution,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0,X2),X0) | r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(sK1,X3) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | r2_hidden(sK1,sK3)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f117])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | r2_hidden(sK1,sK3) | k1_xboole_0 = sK2),
% 0.20/0.49    inference(resolution,[],[f99,f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    r2_hidden(sK3,sK2) | k1_xboole_0 = sK2),
% 0.20/0.49    inference(subsumption_resolution,[],[f76,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k1_setfam_1(sK2)) | r2_hidden(sK3,sK2) | k1_xboole_0 = sK2),
% 0.20/0.49    inference(superposition,[],[f14,f45])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | r2_hidden(sK3,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | r2_hidden(sK1,k1_setfam_1(sK2)) | r2_hidden(sK3,sK2)),
% 0.20/0.49    inference(resolution,[],[f74,f14])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_xboole_0 = sK2 | r2_hidden(sK1,X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | ~r2_hidden(X0,sK2) | r2_hidden(sK1,X0)) )),
% 0.20/0.49    inference(resolution,[],[f81,f38])).
% 0.20/0.49  % (22265)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X3] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.20/0.49    inference(equality_resolution,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2),
% 0.20/0.49    inference(superposition,[],[f74,f45])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | r2_hidden(sK3,k1_xboole_0)),
% 0.20/0.49    inference(forward_demodulation,[],[f126,f125])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    r2_hidden(sK3,k1_xboole_0) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.20/0.49    inference(backward_demodulation,[],[f14,f125])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (22273)------------------------------
% 0.20/0.49  % (22273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22273)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (22273)Memory used [KB]: 1663
% 0.20/0.49  % (22273)Time elapsed: 0.054 s
% 0.20/0.49  % (22273)------------------------------
% 0.20/0.49  % (22273)------------------------------
% 0.20/0.49  % (22257)Success in time 0.142 s
%------------------------------------------------------------------------------
