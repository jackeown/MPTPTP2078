%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:06 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   48 (  79 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 168 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f269,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f131,f255,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f255,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(backward_demodulation,[],[f50,f250])).

fof(f250,plain,(
    k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)) = k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f140,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f140,plain,(
    m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f77,f41])).

fof(f41,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f19,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f70,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f70,plain,(
    ! [X0] : r2_hidden(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f62,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),sK0) ),
    inference(unit_resulting_resolution,[],[f24,f57,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f57,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f47,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f21,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f50,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(backward_demodulation,[],[f20,f45])).

fof(f45,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f21,f26])).

fof(f20,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f131,plain,(
    ! [X0] : r1_tarski(k9_subset_1(sK0,X0,sK2),X0) ),
    inference(superposition,[],[f24,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (818216963)
% 0.13/0.37  ipcrm: permission denied for id (818282505)
% 0.13/0.40  ipcrm: permission denied for id (818380830)
% 0.13/0.40  ipcrm: permission denied for id (818413600)
% 0.19/0.40  ipcrm: permission denied for id (818446373)
% 0.19/0.43  ipcrm: permission denied for id (818577463)
% 0.19/0.43  ipcrm: permission denied for id (818610232)
% 0.19/0.45  ipcrm: permission denied for id (818708561)
% 0.19/0.46  ipcrm: permission denied for id (818741330)
% 0.19/0.47  ipcrm: permission denied for id (818905186)
% 0.19/0.48  ipcrm: permission denied for id (818937958)
% 0.19/0.50  ipcrm: permission denied for id (819101815)
% 0.19/0.50  ipcrm: permission denied for id (819134585)
% 0.19/0.50  ipcrm: permission denied for id (819167356)
% 0.97/0.62  % (11491)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.97/0.62  % (11500)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.06/0.65  % (11485)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.06/0.65  % (11477)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.06/0.66  % (11479)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.06/0.66  % (11493)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.06/0.66  % (11479)Refutation found. Thanks to Tanya!
% 1.06/0.66  % SZS status Theorem for theBenchmark
% 1.06/0.66  % SZS output start Proof for theBenchmark
% 1.06/0.66  fof(f269,plain,(
% 1.06/0.66    $false),
% 1.06/0.66    inference(unit_resulting_resolution,[],[f131,f255,f23])).
% 1.06/0.66  fof(f23,plain,(
% 1.06/0.66    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 1.06/0.66    inference(cnf_transformation,[],[f15])).
% 1.06/0.66  fof(f15,plain,(
% 1.06/0.66    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.06/0.66    inference(ennf_transformation,[],[f2])).
% 1.06/0.66  fof(f2,axiom,(
% 1.06/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.06/0.66  fof(f255,plain,(
% 1.06/0.66    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 1.06/0.66    inference(backward_demodulation,[],[f50,f250])).
% 1.06/0.66  fof(f250,plain,(
% 1.06/0.66    k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)) = k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))),
% 1.06/0.66    inference(unit_resulting_resolution,[],[f140,f26])).
% 1.06/0.66  fof(f26,plain,(
% 1.06/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.06/0.66    inference(cnf_transformation,[],[f17])).
% 1.06/0.66  fof(f17,plain,(
% 1.06/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.06/0.66    inference(ennf_transformation,[],[f7])).
% 1.06/0.66  fof(f7,axiom,(
% 1.06/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.06/0.66  fof(f140,plain,(
% 1.06/0.66    m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.06/0.66    inference(superposition,[],[f77,f41])).
% 1.06/0.66  fof(f41,plain,(
% 1.06/0.66    ( ! [X0] : (k9_subset_1(sK0,X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2))) )),
% 1.06/0.66    inference(unit_resulting_resolution,[],[f19,f37])).
% 1.06/0.66  fof(f37,plain,(
% 1.06/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 1.06/0.66    inference(definition_unfolding,[],[f25,f31])).
% 1.06/0.66  fof(f31,plain,(
% 1.06/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.06/0.66    inference(cnf_transformation,[],[f4])).
% 1.06/0.66  fof(f4,axiom,(
% 1.06/0.66    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.06/0.66  fof(f25,plain,(
% 1.06/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.06/0.66    inference(cnf_transformation,[],[f16])).
% 1.06/0.66  fof(f16,plain,(
% 1.06/0.66    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.06/0.66    inference(ennf_transformation,[],[f9])).
% 1.06/0.66  fof(f9,axiom,(
% 1.06/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.06/0.66  fof(f19,plain,(
% 1.06/0.66    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.06/0.66    inference(cnf_transformation,[],[f12])).
% 1.06/0.66  fof(f12,plain,(
% 1.06/0.66    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.06/0.66    inference(ennf_transformation,[],[f11])).
% 1.06/0.66  fof(f11,negated_conjecture,(
% 1.06/0.66    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 1.06/0.66    inference(negated_conjecture,[],[f10])).
% 1.06/0.66  fof(f10,conjecture,(
% 1.06/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 1.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).
% 1.06/0.66  fof(f77,plain,(
% 1.06/0.66    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))) )),
% 1.06/0.66    inference(unit_resulting_resolution,[],[f36,f70,f29])).
% 1.06/0.66  fof(f29,plain,(
% 1.06/0.66    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.06/0.66    inference(cnf_transformation,[],[f18])).
% 1.06/0.66  fof(f18,plain,(
% 1.06/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.06/0.66    inference(ennf_transformation,[],[f6])).
% 1.06/0.66  fof(f6,axiom,(
% 1.06/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.06/0.66  fof(f70,plain,(
% 1.06/0.66    ( ! [X0] : (r2_hidden(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))) )),
% 1.06/0.66    inference(unit_resulting_resolution,[],[f62,f39])).
% 1.06/0.66  fof(f39,plain,(
% 1.06/0.66    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 1.06/0.66    inference(equality_resolution,[],[f32])).
% 1.06/0.66  fof(f32,plain,(
% 1.06/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.06/0.66    inference(cnf_transformation,[],[f5])).
% 1.06/0.66  fof(f5,axiom,(
% 1.06/0.66    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.06/0.66  fof(f62,plain,(
% 1.06/0.66    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),sK0)) )),
% 1.06/0.66    inference(unit_resulting_resolution,[],[f24,f57,f22])).
% 1.06/0.66  fof(f22,plain,(
% 1.06/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.06/0.66    inference(cnf_transformation,[],[f14])).
% 1.06/0.66  fof(f14,plain,(
% 1.06/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.06/0.66    inference(flattening,[],[f13])).
% 1.06/0.66  fof(f13,plain,(
% 1.06/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.06/0.66    inference(ennf_transformation,[],[f1])).
% 1.06/0.66  fof(f1,axiom,(
% 1.06/0.66    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.06/0.66  fof(f57,plain,(
% 1.06/0.66    r1_tarski(sK1,sK0)),
% 1.06/0.66    inference(unit_resulting_resolution,[],[f47,f38])).
% 1.06/0.66  fof(f38,plain,(
% 1.06/0.66    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.06/0.66    inference(equality_resolution,[],[f33])).
% 1.06/0.66  fof(f33,plain,(
% 1.06/0.66    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.06/0.66    inference(cnf_transformation,[],[f5])).
% 1.06/0.66  fof(f47,plain,(
% 1.06/0.66    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.06/0.66    inference(unit_resulting_resolution,[],[f36,f21,f30])).
% 1.06/0.66  fof(f30,plain,(
% 1.06/0.66    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 1.06/0.66    inference(cnf_transformation,[],[f18])).
% 1.06/0.66  fof(f21,plain,(
% 1.06/0.66    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.06/0.66    inference(cnf_transformation,[],[f12])).
% 1.06/0.66  fof(f24,plain,(
% 1.06/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.06/0.66    inference(cnf_transformation,[],[f3])).
% 1.06/0.66  fof(f3,axiom,(
% 1.06/0.66    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.06/0.66  fof(f36,plain,(
% 1.06/0.66    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.06/0.66    inference(cnf_transformation,[],[f8])).
% 1.06/0.66  fof(f8,axiom,(
% 1.06/0.66    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.06/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.06/0.66  fof(f50,plain,(
% 1.06/0.66    ~r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 1.06/0.66    inference(backward_demodulation,[],[f20,f45])).
% 1.06/0.66  fof(f45,plain,(
% 1.06/0.66    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.06/0.66    inference(unit_resulting_resolution,[],[f21,f26])).
% 1.06/0.66  fof(f20,plain,(
% 1.06/0.66    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 1.06/0.66    inference(cnf_transformation,[],[f12])).
% 1.06/0.66  fof(f131,plain,(
% 1.06/0.66    ( ! [X0] : (r1_tarski(k9_subset_1(sK0,X0,sK2),X0)) )),
% 1.06/0.66    inference(superposition,[],[f24,f41])).
% 1.06/0.66  % SZS output end Proof for theBenchmark
% 1.06/0.66  % (11479)------------------------------
% 1.06/0.66  % (11479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.66  % (11479)Termination reason: Refutation
% 1.06/0.66  
% 1.06/0.66  % (11479)Memory used [KB]: 6396
% 1.06/0.66  % (11479)Time elapsed: 0.110 s
% 1.06/0.66  % (11479)------------------------------
% 1.06/0.66  % (11479)------------------------------
% 1.06/0.66  % (11341)Success in time 0.308 s
%------------------------------------------------------------------------------
