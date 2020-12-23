%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:41 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 169 expanded)
%              Number of leaves         :    8 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  135 ( 533 expanded)
%              Number of equality atoms :   10 (  46 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(subsumption_resolution,[],[f141,f127])).

fof(f127,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f126,f18])).

fof(f18,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(f126,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = sK2 ),
    inference(resolution,[],[f121,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f121,plain,(
    r1_tarski(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f116,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | r1_tarski(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | r1_tarski(sK2,X0)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f53,f73])).

fof(f73,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK2,X1),sK0)
      | r1_tarski(sK2,X1) ) ),
    inference(resolution,[],[f66,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK2)
      | r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f32,f51])).

fof(f51,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f49,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f28,f21])).

fof(f21,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f49,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f46,f20])).

fof(f20,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f46,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f27,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK2,X0),sK0)
      | r2_hidden(sK4(sK2,X0),sK1)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f33,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f15,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f141,plain,(
    r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f140,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f65,f33])).

fof(f65,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(X5,sK0) ) ),
    inference(resolution,[],[f32,f52])).

fof(f52,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f50,f43])).

fof(f50,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f47,f20])).

fof(f47,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f27,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f140,plain,(
    ~ r2_hidden(sK4(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f138,f127])).

fof(f138,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK4(sK1,sK2),sK0) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK4(sK1,sK2),sK0)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f56,f33])).

fof(f56,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(X1,sK2),sK1)
      | r1_tarski(X1,sK2)
      | ~ r2_hidden(sK4(X1,sK2),sK0) ) ),
    inference(resolution,[],[f34,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f16,f37])).

fof(f16,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:06:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (13920)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (13919)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.15/0.51  % (13925)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.15/0.51  % (13916)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.15/0.52  % (13935)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.15/0.52  % (13914)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.15/0.52  % (13916)Refutation found. Thanks to Tanya!
% 1.15/0.52  % SZS status Theorem for theBenchmark
% 1.15/0.52  % SZS output start Proof for theBenchmark
% 1.15/0.52  fof(f142,plain,(
% 1.15/0.52    $false),
% 1.15/0.52    inference(subsumption_resolution,[],[f141,f127])).
% 1.15/0.52  fof(f127,plain,(
% 1.15/0.52    ~r1_tarski(sK1,sK2)),
% 1.15/0.52    inference(subsumption_resolution,[],[f126,f18])).
% 1.15/0.52  fof(f18,plain,(
% 1.15/0.52    sK1 != sK2),
% 1.15/0.52    inference(cnf_transformation,[],[f11])).
% 1.15/0.52  fof(f11,plain,(
% 1.15/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.15/0.52    inference(flattening,[],[f10])).
% 1.15/0.52  fof(f10,plain,(
% 1.15/0.52    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.15/0.52    inference(ennf_transformation,[],[f9])).
% 1.15/0.52  fof(f9,negated_conjecture,(
% 1.15/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.15/0.52    inference(negated_conjecture,[],[f8])).
% 1.15/0.52  fof(f8,conjecture,(
% 1.15/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.15/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 1.15/0.52  fof(f126,plain,(
% 1.15/0.52    ~r1_tarski(sK1,sK2) | sK1 = sK2),
% 1.15/0.52    inference(resolution,[],[f121,f31])).
% 1.15/0.52  fof(f31,plain,(
% 1.15/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.15/0.52    inference(cnf_transformation,[],[f3])).
% 1.15/0.52  fof(f3,axiom,(
% 1.15/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.15/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.15/0.52  fof(f121,plain,(
% 1.15/0.52    r1_tarski(sK2,sK1)),
% 1.15/0.52    inference(duplicate_literal_removal,[],[f117])).
% 1.15/0.52  fof(f117,plain,(
% 1.15/0.52    r1_tarski(sK2,sK1) | r1_tarski(sK2,sK1)),
% 1.15/0.52    inference(resolution,[],[f116,f34])).
% 1.15/0.52  fof(f34,plain,(
% 1.15/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f14])).
% 1.15/0.52  fof(f14,plain,(
% 1.15/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.15/0.52    inference(ennf_transformation,[],[f2])).
% 1.15/0.52  fof(f2,axiom,(
% 1.15/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.15/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.15/0.52  fof(f116,plain,(
% 1.15/0.52    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK1) | r1_tarski(sK2,X0)) )),
% 1.15/0.52    inference(duplicate_literal_removal,[],[f115])).
% 1.15/0.52  fof(f115,plain,(
% 1.15/0.52    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK1) | r1_tarski(sK2,X0) | r1_tarski(sK2,X0)) )),
% 1.15/0.52    inference(resolution,[],[f53,f73])).
% 1.15/0.52  fof(f73,plain,(
% 1.15/0.52    ( ! [X1] : (r2_hidden(sK4(sK2,X1),sK0) | r1_tarski(sK2,X1)) )),
% 1.15/0.52    inference(resolution,[],[f66,f33])).
% 1.15/0.52  fof(f33,plain,(
% 1.15/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f14])).
% 1.15/0.52  fof(f66,plain,(
% 1.15/0.52    ( ! [X6] : (~r2_hidden(X6,sK2) | r2_hidden(X6,sK0)) )),
% 1.15/0.52    inference(resolution,[],[f32,f51])).
% 1.15/0.52  fof(f51,plain,(
% 1.15/0.52    r1_tarski(sK2,sK0)),
% 1.15/0.52    inference(resolution,[],[f49,f43])).
% 1.15/0.52  fof(f43,plain,(
% 1.15/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) )),
% 1.15/0.52    inference(superposition,[],[f28,f21])).
% 1.15/0.52  fof(f21,plain,(
% 1.15/0.52    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.15/0.52    inference(cnf_transformation,[],[f5])).
% 1.15/0.52  fof(f5,axiom,(
% 1.15/0.52    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.15/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.15/0.52  fof(f28,plain,(
% 1.15/0.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f13])).
% 1.15/0.52  fof(f13,plain,(
% 1.15/0.52    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.15/0.52    inference(ennf_transformation,[],[f4])).
% 1.15/0.52  fof(f4,axiom,(
% 1.15/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.15/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.15/0.52  fof(f49,plain,(
% 1.15/0.52    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.15/0.52    inference(subsumption_resolution,[],[f46,f20])).
% 1.15/0.52  fof(f20,plain,(
% 1.15/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.15/0.52    inference(cnf_transformation,[],[f7])).
% 1.15/0.52  fof(f7,axiom,(
% 1.15/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.15/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.15/0.52  fof(f46,plain,(
% 1.15/0.52    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.15/0.52    inference(resolution,[],[f27,f17])).
% 1.15/0.52  fof(f17,plain,(
% 1.15/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.15/0.52    inference(cnf_transformation,[],[f11])).
% 1.15/0.52  fof(f27,plain,(
% 1.15/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f12])).
% 1.15/0.52  fof(f12,plain,(
% 1.15/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.15/0.52    inference(ennf_transformation,[],[f6])).
% 1.15/0.52  fof(f6,axiom,(
% 1.15/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.15/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.15/0.52  fof(f32,plain,(
% 1.15/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f14])).
% 1.15/0.52  fof(f53,plain,(
% 1.15/0.52    ( ! [X0] : (~r2_hidden(sK4(sK2,X0),sK0) | r2_hidden(sK4(sK2,X0),sK1) | r1_tarski(sK2,X0)) )),
% 1.15/0.52    inference(resolution,[],[f33,f38])).
% 1.15/0.52  fof(f38,plain,(
% 1.15/0.52    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 1.15/0.52    inference(resolution,[],[f15,f37])).
% 1.15/0.52  fof(f37,plain,(
% 1.15/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.15/0.52    inference(subsumption_resolution,[],[f26,f23])).
% 1.15/0.52  fof(f23,plain,(
% 1.15/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f1])).
% 1.15/0.52  fof(f1,axiom,(
% 1.15/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.15/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.15/0.52  fof(f26,plain,(
% 1.15/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f12])).
% 1.15/0.52  fof(f15,plain,(
% 1.15/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f11])).
% 1.15/0.52  fof(f141,plain,(
% 1.15/0.52    r1_tarski(sK1,sK2)),
% 1.15/0.52    inference(resolution,[],[f140,f70])).
% 1.15/0.52  fof(f70,plain,(
% 1.15/0.52    ( ! [X0] : (r2_hidden(sK4(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 1.15/0.52    inference(resolution,[],[f65,f33])).
% 1.15/0.52  fof(f65,plain,(
% 1.15/0.52    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,sK0)) )),
% 1.15/0.52    inference(resolution,[],[f32,f52])).
% 1.15/0.52  fof(f52,plain,(
% 1.15/0.52    r1_tarski(sK1,sK0)),
% 1.15/0.52    inference(resolution,[],[f50,f43])).
% 1.15/0.52  fof(f50,plain,(
% 1.15/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.15/0.52    inference(subsumption_resolution,[],[f47,f20])).
% 1.15/0.52  fof(f47,plain,(
% 1.15/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.15/0.52    inference(resolution,[],[f27,f19])).
% 1.15/0.52  fof(f19,plain,(
% 1.15/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.15/0.52    inference(cnf_transformation,[],[f11])).
% 1.15/0.52  fof(f140,plain,(
% 1.15/0.52    ~r2_hidden(sK4(sK1,sK2),sK0)),
% 1.15/0.52    inference(subsumption_resolution,[],[f138,f127])).
% 1.15/0.52  fof(f138,plain,(
% 1.15/0.52    r1_tarski(sK1,sK2) | ~r2_hidden(sK4(sK1,sK2),sK0)),
% 1.15/0.52    inference(duplicate_literal_removal,[],[f137])).
% 1.15/0.52  fof(f137,plain,(
% 1.15/0.52    r1_tarski(sK1,sK2) | ~r2_hidden(sK4(sK1,sK2),sK0) | r1_tarski(sK1,sK2)),
% 1.15/0.52    inference(resolution,[],[f56,f33])).
% 1.15/0.52  fof(f56,plain,(
% 1.15/0.52    ( ! [X1] : (~r2_hidden(sK4(X1,sK2),sK1) | r1_tarski(X1,sK2) | ~r2_hidden(sK4(X1,sK2),sK0)) )),
% 1.15/0.52    inference(resolution,[],[f34,f39])).
% 1.15/0.52  fof(f39,plain,(
% 1.15/0.52    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 1.15/0.52    inference(resolution,[],[f16,f37])).
% 1.15/0.52  fof(f16,plain,(
% 1.15/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f11])).
% 1.15/0.52  % SZS output end Proof for theBenchmark
% 1.15/0.52  % (13916)------------------------------
% 1.15/0.52  % (13916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.52  % (13916)Termination reason: Refutation
% 1.15/0.52  
% 1.15/0.52  % (13916)Memory used [KB]: 6268
% 1.15/0.52  % (13916)Time elapsed: 0.045 s
% 1.15/0.52  % (13916)------------------------------
% 1.15/0.52  % (13916)------------------------------
% 1.15/0.52  % (13920)Refutation not found, incomplete strategy% (13920)------------------------------
% 1.15/0.52  % (13920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.52  % (13920)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.52  
% 1.15/0.52  % (13920)Memory used [KB]: 10618
% 1.15/0.52  % (13920)Time elapsed: 0.113 s
% 1.15/0.52  % (13920)------------------------------
% 1.15/0.52  % (13920)------------------------------
% 1.29/0.53  % (13905)Success in time 0.163 s
%------------------------------------------------------------------------------
