%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 122 expanded)
%              Number of leaves         :    3 (  23 expanded)
%              Depth                    :   16
%              Number of atoms          :   84 ( 480 expanded)
%              Number of equality atoms :   16 (  90 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(subsumption_resolution,[],[f46,f13])).

fof(f13,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f46,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f44,f37])).

fof(f37,plain,(
    r2_hidden(sK3(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f35,f13])).

fof(f35,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | sK1 = sK2 ),
    inference(factoring,[],[f31])).

% (24036)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (24021)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (24034)Refutation not found, incomplete strategy% (24034)------------------------------
% (24034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f31,plain,(
    ! [X1] :
      ( r2_hidden(sK3(X1,sK2),X1)
      | r2_hidden(sK3(X1,sK2),sK1)
      | sK2 = X1 ) ),
    inference(subsumption_resolution,[],[f29,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f29,plain,(
    ! [X1] :
      ( r2_hidden(sK3(X1,sK2),X1)
      | sK2 = X1
      | ~ r2_hidden(sK3(X1,sK2),sK2)
      | r2_hidden(sK3(X1,sK2),sK1) ) ),
    inference(resolution,[],[f24,f10])).

fof(f10,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,sK2),X0)
      | m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(sK0))
      | sK2 = X0 ) ),
    inference(resolution,[],[f18,f12])).

fof(f12,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | X0 = X1
      | r2_hidden(sK3(X0,X1),X0)
      | m1_subset_1(sK3(X0,X1),X2) ) ),
    inference(resolution,[],[f15,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f44,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f43,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f43,plain,(
    r2_hidden(sK3(sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f40,f37])).

fof(f40,plain,
    ( r2_hidden(sK3(sK1,sK2),sK2)
    | ~ r2_hidden(sK3(sK1,sK2),sK1) ),
    inference(resolution,[],[f39,f11])).

fof(f11,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f38,f14])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(sK1,sK2),X0) ) ),
    inference(resolution,[],[f37,f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:07:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (24026)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (24034)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (24018)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (24018)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f46,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    sK1 != sK2),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(flattening,[],[f5])).
% 0.22/0.51  fof(f5,plain,(
% 0.22/0.51    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.51    inference(negated_conjecture,[],[f3])).
% 0.22/0.51  fof(f3,conjecture,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    sK1 = sK2),
% 0.22/0.51    inference(subsumption_resolution,[],[f44,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    r2_hidden(sK3(sK1,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f35,f13])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    r2_hidden(sK3(sK1,sK2),sK1) | sK1 = sK2),
% 0.22/0.51    inference(factoring,[],[f31])).
% 0.22/0.51  % (24036)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.51  % (24021)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (24034)Refutation not found, incomplete strategy% (24034)------------------------------
% 0.22/0.52  % (24034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(sK3(X1,sK2),X1) | r2_hidden(sK3(X1,sK2),sK1) | sK2 = X1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f29,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(sK3(X1,sK2),X1) | sK2 = X1 | ~r2_hidden(sK3(X1,sK2),sK2) | r2_hidden(sK3(X1,sK2),sK1)) )),
% 0.22/0.52    inference(resolution,[],[f24,f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(X0,sK2),X0) | m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(sK0)) | sK2 = X0) )),
% 0.22/0.52    inference(resolution,[],[f18,f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | X0 = X1 | r2_hidden(sK3(X0,X1),X0) | m1_subset_1(sK3(X0,X1),X2)) )),
% 0.22/0.52    inference(resolution,[],[f15,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK1,sK2),sK1) | sK1 = sK2),
% 0.22/0.52    inference(resolution,[],[f43,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    r2_hidden(sK3(sK1,sK2),sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f40,f37])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    r2_hidden(sK3(sK1,sK2),sK2) | ~r2_hidden(sK3(sK1,sK2),sK1)),
% 0.22/0.52    inference(resolution,[],[f39,f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(resolution,[],[f38,f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | m1_subset_1(sK3(sK1,sK2),X0)) )),
% 0.22/0.52    inference(resolution,[],[f37,f17])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (24018)------------------------------
% 0.22/0.52  % (24018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (24018)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (24018)Memory used [KB]: 6140
% 0.22/0.52  % (24018)Time elapsed: 0.084 s
% 0.22/0.52  % (24018)------------------------------
% 0.22/0.52  % (24018)------------------------------
% 0.22/0.52  % (24011)Success in time 0.146 s
%------------------------------------------------------------------------------
