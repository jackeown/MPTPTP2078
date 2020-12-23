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
% DateTime   : Thu Dec  3 13:11:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  45 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 104 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(global_subsumption,[],[f34,f43])).

fof(f43,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(resolution,[],[f42,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(resolution,[],[f39,f24])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK1(X0,k1_xboole_0))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,sK1(X0,X1))
      | ~ l1_pre_topc(X0)
      | k1_struct_0(X0) = X1 ) ),
    inference(resolution,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | k1_struct_0(X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(sK1(X0,X1),X1)
            & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )
          | k1_struct_0(X0) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_struct_0(X0) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_struct_0(X0) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r2_hidden(X2,X1) )
              & k1_struct_0(X0) != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_pre_topc)).

fof(f34,plain,(
    k1_xboole_0 != k1_struct_0(sK0) ),
    inference(superposition,[],[f23,f33])).

fof(f33,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(resolution,[],[f32,f22])).

fof(f32,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(resolution,[],[f27,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_tops_1)).

fof(f23,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (6258)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.41  % (6256)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (6255)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.41  % (6255)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(global_subsumption,[],[f34,f43])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    k1_xboole_0 = k1_struct_0(sK0)),
% 0.21/0.41    inference(resolution,[],[f42,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    l1_pre_topc(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f19])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0)) => (k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,negated_conjecture,(
% 0.21/0.41    ~! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.21/0.41    inference(negated_conjecture,[],[f8])).
% 0.21/0.41  fof(f8,conjecture,(
% 0.21/0.41    ! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.41    inference(resolution,[],[f39,f24])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK1(X0,k1_xboole_0)) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.41    inference(resolution,[],[f38,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.41  fof(f38,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,sK1(X0,X1)) | ~l1_pre_topc(X0) | k1_struct_0(X0) = X1) )),
% 0.21/0.41    inference(resolution,[],[f29,f30])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f21])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : ((r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f20])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(flattening,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | k1_struct_0(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r2_hidden(X2,X1)) & k1_struct_0(X0) != X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_pre_topc)).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    k1_xboole_0 != k1_struct_0(sK0)),
% 0.21/0.41    inference(superposition,[],[f23,f33])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    k1_xboole_0 = k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.41    inference(resolution,[],[f32,f22])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,k1_struct_0(X0))) )),
% 0.21/0.41    inference(resolution,[],[f27,f26])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    ( ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,axiom,(
% 0.21/0.41    ! [X0] : (l1_pre_topc(X0) => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_tops_1)).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.41    inference(cnf_transformation,[],[f19])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (6255)------------------------------
% 0.21/0.41  % (6255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (6255)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (6255)Memory used [KB]: 6140
% 0.21/0.41  % (6255)Time elapsed: 0.004 s
% 0.21/0.41  % (6255)------------------------------
% 0.21/0.41  % (6255)------------------------------
% 0.21/0.42  % (6250)Success in time 0.06 s
%------------------------------------------------------------------------------
