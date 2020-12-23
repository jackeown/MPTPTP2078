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
% DateTime   : Thu Dec  3 12:46:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 105 expanded)
%              Number of leaves         :    5 (  22 expanded)
%              Depth                    :   15
%              Number of atoms          :  141 ( 354 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(subsumption_resolution,[],[f217,f17])).

fof(f17,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

fof(f217,plain,(
    r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f214,f28])).

fof(f28,plain,(
    r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f27,f15])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f214,plain,
    ( ~ r1_tarski(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f191,f157])).

fof(f157,plain,(
    ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f155,f17])).

fof(f155,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) ),
    inference(resolution,[],[f132,f28])).

fof(f132,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X1)
      | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X1),X1) ) ),
    inference(resolution,[],[f45,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ r2_hidden(sK3(X3,X2,X4),X4)
      | r1_tarski(X2,X4)
      | ~ r1_tarski(X4,X3) ) ),
    inference(resolution,[],[f23,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f191,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X0),sK2)
      | ~ r1_tarski(X0,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f181,f127])).

fof(f127,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X1),sK1)
      | r1_tarski(sK1,X1)
      | ~ r1_tarski(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f42,f18])).

fof(f42,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | r2_hidden(sK3(X3,X2,X4),X2)
      | r1_tarski(X2,X4)
      | ~ r1_tarski(X4,X3) ) ),
    inference(resolution,[],[f22,f26])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f181,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ r1_tarski(X0,k1_zfmisc_1(sK0))
      | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X0),sK2)
      | ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X0),sK1) ) ),
    inference(resolution,[],[f122,f160])).

fof(f160,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f159,f18])).

fof(f159,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(resolution,[],[f55,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f54,f15])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(X0,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(resolution,[],[f48,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(X0,k7_setfam_1(sK0,sK2))
      | ~ r2_hidden(X0,k7_setfam_1(sK0,sK1)) ) ),
    inference(resolution,[],[f33,f16])).

fof(f16,plain,(
    r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X4)
      | r2_hidden(X2,X4)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f20,f26])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f122,plain,(
    ! [X1] :
      ( m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,X1),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X1)
      | ~ r1_tarski(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f39,f18])).

fof(f39,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | m1_subset_1(sK3(X3,X2,X4),X3)
      | r1_tarski(X2,X4)
      | ~ r1_tarski(X4,X3) ) ),
    inference(resolution,[],[f21,f26])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:44:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.40  % (17282)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.41  % (17277)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.41  % (17276)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.42  % (17276)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f218,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f217,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ~r1_tarski(sK1,sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.42    inference(flattening,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).
% 0.21/0.42  fof(f217,plain,(
% 0.21/0.42    r1_tarski(sK1,sK2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f214,f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    r1_tarski(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(resolution,[],[f27,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.42  fof(f214,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK2)),
% 0.21/0.42    inference(resolution,[],[f191,f157])).
% 0.21/0.42  fof(f157,plain,(
% 0.21/0.42    ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f155,f17])).
% 0.21/0.42  fof(f155,plain,(
% 0.21/0.42    r1_tarski(sK1,sK2) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)),
% 0.21/0.42    inference(resolution,[],[f132,f28])).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    ( ! [X1] : (~r1_tarski(X1,k1_zfmisc_1(sK0)) | r1_tarski(sK1,X1) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X1),X1)) )),
% 0.21/0.42    inference(resolution,[],[f45,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~r2_hidden(sK3(X3,X2,X4),X4) | r1_tarski(X2,X4) | ~r1_tarski(X4,X3)) )),
% 0.21/0.42    inference(resolution,[],[f23,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK3(X0,X1,X2),X2) | r1_tarski(X1,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 0.21/0.42  fof(f191,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X0),sK2) | ~r1_tarski(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK1,X0)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f181,f127])).
% 0.21/0.42  fof(f127,plain,(
% 0.21/0.42    ( ! [X1] : (r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X1),sK1) | r1_tarski(sK1,X1) | ~r1_tarski(X1,k1_zfmisc_1(sK0))) )),
% 0.21/0.42    inference(resolution,[],[f42,f18])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | r2_hidden(sK3(X3,X2,X4),X2) | r1_tarski(X2,X4) | ~r1_tarski(X4,X3)) )),
% 0.21/0.42    inference(resolution,[],[f22,f26])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f181,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(sK1,X0) | ~r1_tarski(X0,k1_zfmisc_1(sK0)) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X0),sK2) | ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,X0),sK1)) )),
% 0.21/0.42    inference(resolution,[],[f122,f160])).
% 0.21/0.42  fof(f160,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f159,f18])).
% 0.21/0.42  fof(f159,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f158])).
% 0.21/0.42  fof(f158,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.42    inference(resolution,[],[f55,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(X0,sK2)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f54,f15])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(k3_subset_1(sK0,X0),k7_setfam_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(X0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.42    inference(resolution,[],[f48,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(X0,k7_setfam_1(sK0,sK2)) | ~r2_hidden(X0,k7_setfam_1(sK0,sK1))) )),
% 0.21/0.42    inference(resolution,[],[f33,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X4,X2,X3] : (~r1_tarski(X3,X4) | r2_hidden(X2,X4) | ~r2_hidden(X2,X3)) )),
% 0.21/0.42    inference(resolution,[],[f20,f26])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.42  fof(f122,plain,(
% 0.21/0.42    ( ! [X1] : (m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,X1),k1_zfmisc_1(sK0)) | r1_tarski(sK1,X1) | ~r1_tarski(X1,k1_zfmisc_1(sK0))) )),
% 0.21/0.42    inference(resolution,[],[f39,f18])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | m1_subset_1(sK3(X3,X2,X4),X3) | r1_tarski(X2,X4) | ~r1_tarski(X4,X3)) )),
% 0.21/0.42    inference(resolution,[],[f21,f26])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2),X0) | r1_tarski(X1,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (17276)------------------------------
% 0.21/0.42  % (17276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (17276)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (17276)Memory used [KB]: 10746
% 0.21/0.42  % (17276)Time elapsed: 0.012 s
% 0.21/0.42  % (17276)------------------------------
% 0.21/0.42  % (17276)------------------------------
% 0.21/0.42  % (17272)Success in time 0.068 s
%------------------------------------------------------------------------------
