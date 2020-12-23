%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 170 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :   18
%              Number of atoms          :  158 ( 544 expanded)
%              Number of equality atoms :   18 (  56 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(subsumption_resolution,[],[f187,f121])).

fof(f121,plain,(
    r1_tarski(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f116,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(resolution,[],[f56,f73])).

fof(f73,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK2,X1),sK0)
      | r1_tarski(sK2,X1) ) ),
    inference(resolution,[],[f66,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK2)
      | r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f35,f54])).

fof(f54,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f52,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f33,f26])).

fof(f26,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f52,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f49,f25])).

fof(f25,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f49,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK2,X0),sK0)
      | r2_hidden(sK4(sK2,X0),sK1)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f36,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f20,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f31,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

% (27415)Termination reason: Refutation not found, incomplete strategy
fof(f20,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f187,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f182,f23])).

fof(f23,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f182,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f176,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK2,X0),sK1)
      | sK2 = X0
      | ~ r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f122,f65])).

fof(f65,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(X5,sK0) ) ),
    inference(resolution,[],[f35,f55])).

fof(f55,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f53,f46])).

fof(f53,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f50,f25])).

fof(f50,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | sK2 = X0
      | ~ r2_hidden(sK5(sK2,X0),sK1)
      | ~ r2_hidden(sK5(sK2,X0),sK0) ) ),
    inference(resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f21,f40])).

fof(f21,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f34,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f176,plain,(
    r2_hidden(sK5(sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f170,f23])).

fof(f170,plain,
    ( sK1 = sK2
    | r2_hidden(sK5(sK2,sK1),sK1) ),
    inference(resolution,[],[f62,f121])).

fof(f62,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | X2 = X3
      | r2_hidden(sK5(X2,X3),X3) ) ),
    inference(resolution,[],[f34,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:15:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (27419)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (27419)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (27415)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (27442)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (27415)Refutation not found, incomplete strategy% (27415)------------------------------
% 0.21/0.56  % (27415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f188,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f187,f121])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    r1_tarski(sK2,sK1)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f117])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    r1_tarski(sK2,sK1) | r1_tarski(sK2,sK1)),
% 0.21/0.57    inference(resolution,[],[f116,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK1) | r1_tarski(sK2,X0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f115])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK1) | r1_tarski(sK2,X0) | r1_tarski(sK2,X0)) )),
% 0.21/0.57    inference(resolution,[],[f56,f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X1] : (r2_hidden(sK4(sK2,X1),sK0) | r1_tarski(sK2,X1)) )),
% 0.21/0.57    inference(resolution,[],[f66,f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X6] : (~r2_hidden(X6,sK2) | r2_hidden(X6,sK0)) )),
% 0.21/0.57    inference(resolution,[],[f35,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    r1_tarski(sK2,sK0)),
% 0.21/0.57    inference(resolution,[],[f52,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) )),
% 0.21/0.57    inference(superposition,[],[f33,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(subsumption_resolution,[],[f49,f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f32,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(flattening,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.57    inference(negated_conjecture,[],[f9])).
% 0.21/0.57  fof(f9,conjecture,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(sK4(sK2,X0),sK0) | r2_hidden(sK4(sK2,X0),sK1) | r1_tarski(sK2,X0)) )),
% 0.21/0.57    inference(resolution,[],[f36,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.57    inference(resolution,[],[f20,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f31,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  % (27415)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f187,plain,(
% 0.21/0.57    ~r1_tarski(sK2,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f182,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    sK1 != sK2),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f182,plain,(
% 0.21/0.57    sK1 = sK2 | ~r1_tarski(sK2,sK1)),
% 0.21/0.57    inference(resolution,[],[f176,f123])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(sK5(sK2,X0),sK1) | sK2 = X0 | ~r1_tarski(sK2,X0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f122,f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,sK0)) )),
% 0.21/0.57    inference(resolution,[],[f35,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    r1_tarski(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f53,f46])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(subsumption_resolution,[],[f50,f25])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f32,f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(sK2,X0) | sK2 = X0 | ~r2_hidden(sK5(sK2,X0),sK1) | ~r2_hidden(sK5(sK2,X0),sK0)) )),
% 0.21/0.57    inference(resolution,[],[f61,f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.57    inference(resolution,[],[f21,f40])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.57    inference(resolution,[],[f34,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_hidden(sK5(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.21/0.57    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.57  fof(f176,plain,(
% 0.21/0.57    r2_hidden(sK5(sK2,sK1),sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f170,f23])).
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    sK1 = sK2 | r2_hidden(sK5(sK2,sK1),sK1)),
% 0.21/0.57    inference(resolution,[],[f62,f121])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r1_tarski(X2,X3) | X2 = X3 | r2_hidden(sK5(X2,X3),X3)) )),
% 0.21/0.57    inference(resolution,[],[f34,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK5(X0,X1),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (27419)------------------------------
% 0.21/0.57  % (27419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (27419)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (27419)Memory used [KB]: 6268
% 0.21/0.57  % (27419)Time elapsed: 0.128 s
% 0.21/0.57  % (27419)------------------------------
% 0.21/0.57  % (27419)------------------------------
% 0.21/0.57  
% 0.21/0.57  % (27415)Memory used [KB]: 10746
% 0.21/0.57  % (27415)Time elapsed: 0.129 s
% 0.21/0.57  % (27415)------------------------------
% 0.21/0.57  % (27415)------------------------------
% 0.21/0.57  % (27412)Success in time 0.204 s
%------------------------------------------------------------------------------
