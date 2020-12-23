%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  48 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 111 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(resolution,[],[f71,f24])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f71,plain,(
    ! [X0] : ~ v1_xboole_0(X0) ),
    inference(global_subsumption,[],[f35,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_struct_0(sK0) ) ),
    inference(resolution,[],[f64,f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(resolution,[],[f63,f25])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f63,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X17)))
      | ~ v1_xboole_0(X18)
      | ~ l1_pre_topc(X17)
      | k1_xboole_0 = k1_struct_0(X17) ) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f31,f25])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_struct_0(X0) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_pre_topc)).

fof(f35,plain,(
    k1_xboole_0 != k1_struct_0(sK0) ),
    inference(superposition,[],[f23,f34])).

fof(f34,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(resolution,[],[f33,f22])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(resolution,[],[f26,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_tops_1)).

fof(f23,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (31877)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.41  % (31877)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(resolution,[],[f71,f24])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    v1_xboole_0(k1_xboole_0)),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    v1_xboole_0(k1_xboole_0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.41  fof(f71,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_xboole_0(X0)) )),
% 0.21/0.41    inference(global_subsumption,[],[f35,f70])).
% 0.21/0.41  fof(f70,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_struct_0(sK0)) )),
% 0.21/0.41    inference(resolution,[],[f64,f22])).
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
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.41    inference(resolution,[],[f63,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.41  fof(f63,plain,(
% 0.21/0.41    ( ! [X17,X18] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X17))) | ~v1_xboole_0(X18) | ~l1_pre_topc(X17) | k1_xboole_0 = k1_struct_0(X17)) )),
% 0.21/0.41    inference(resolution,[],[f28,f37])).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~v1_xboole_0(X0)) )),
% 0.21/0.41    inference(resolution,[],[f31,f25])).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f21])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : ((r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | k1_struct_0(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r2_hidden(X2,X1)) & k1_struct_0(X0) != X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_pre_topc)).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    k1_xboole_0 != k1_struct_0(sK0)),
% 0.21/0.42    inference(superposition,[],[f23,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    k1_xboole_0 = k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.42    inference(resolution,[],[f33,f22])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,k1_struct_0(X0))) )),
% 0.21/0.42    inference(resolution,[],[f26,f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_tops_1)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (31877)------------------------------
% 0.21/0.42  % (31877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (31877)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (31877)Memory used [KB]: 6140
% 0.21/0.42  % (31877)Time elapsed: 0.006 s
% 0.21/0.42  % (31877)------------------------------
% 0.21/0.42  % (31877)------------------------------
% 0.21/0.42  % (31866)Success in time 0.063 s
%------------------------------------------------------------------------------
