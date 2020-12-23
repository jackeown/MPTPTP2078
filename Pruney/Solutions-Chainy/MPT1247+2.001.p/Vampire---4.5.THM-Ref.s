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
% DateTime   : Thu Dec  3 13:11:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 119 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 338 expanded)
%              Number of equality atoms :   36 ( 115 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(global_subsumption,[],[f21,f19,f154])).

fof(f154,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f153,f105])).

fof(f105,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(superposition,[],[f104,f65])).

fof(f65,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(global_subsumption,[],[f19,f61])).

fof(f61,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f22,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,X1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,X1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( k2_tops_1(sK0,X1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,X1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

fof(f104,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_xboole_0(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(global_subsumption,[],[f19,f100])).

fof(f100,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_xboole_0(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f46,f20])).

fof(f46,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X3))) = k3_xboole_0(X2,k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X3)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X0)) = k3_xboole_0(X2,k2_pre_topc(X1,X0)) ) ),
    inference(resolution,[],[f26,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f153,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f152,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f152,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f151,f49])).

fof(f49,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(X0,k2_pre_topc(sK0,sK1)) ),
    inference(global_subsumption,[],[f19,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(X0,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f33,f20])).

fof(f151,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f147,f28])).

fof(f28,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f25,f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f147,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f62,f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),X1)))) ) ),
    inference(resolution,[],[f22,f24])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:29:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (14397)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (14396)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.43  % (14399)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (14400)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.44  % (14397)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(global_subsumption,[],[f21,f19,f154])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.44    inference(forward_demodulation,[],[f153,f105])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.21/0.44    inference(superposition,[],[f104,f65])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.21/0.44    inference(global_subsumption,[],[f19,f61])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.44    inference(resolution,[],[f22,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    (k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (k2_tops_1(X0,X1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,X1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X1] : (k2_tops_1(sK0,X1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (k2_tops_1(X0,X1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_xboole_0(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) )),
% 0.21/0.44    inference(global_subsumption,[],[f19,f100])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_xboole_0(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f46,f20])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X3))) = k3_xboole_0(X2,k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X3))) | ~l1_pre_topc(X1)) )),
% 0.21/0.44    inference(resolution,[],[f33,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X0)) = k3_xboole_0(X2,k2_pre_topc(X1,X0))) )),
% 0.21/0.44    inference(resolution,[],[f26,f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.44  fof(f153,plain,(
% 0.21/0.44    k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.44    inference(forward_demodulation,[],[f152,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.44    inference(forward_demodulation,[],[f151,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(X0,k2_pre_topc(sK0,sK1))) )),
% 0.21/0.44    inference(global_subsumption,[],[f19,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_pre_topc(sK0) | k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1)) = k3_xboole_0(X0,k2_pre_topc(sK0,sK1))) )),
% 0.21/0.44    inference(resolution,[],[f33,f20])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.44    inference(forward_demodulation,[],[f147,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.44    inference(resolution,[],[f25,f20])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    ~l1_pre_topc(sK0) | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))),
% 0.21/0.44    inference(resolution,[],[f62,f20])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),X1))))) )),
% 0.21/0.44    inference(resolution,[],[f22,f24])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (14397)------------------------------
% 0.21/0.44  % (14397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (14397)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (14397)Memory used [KB]: 6268
% 0.21/0.44  % (14397)Time elapsed: 0.015 s
% 0.21/0.44  % (14397)------------------------------
% 0.21/0.44  % (14397)------------------------------
% 0.21/0.44  % (14392)Success in time 0.078 s
%------------------------------------------------------------------------------
