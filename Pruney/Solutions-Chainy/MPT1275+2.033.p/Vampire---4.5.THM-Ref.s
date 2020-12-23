%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 241 expanded)
%              Number of leaves         :    6 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  163 ( 921 expanded)
%              Number of equality atoms :   28 ( 175 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(global_subsumption,[],[f49,f57,f58])).

fof(f58,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f56,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f56,plain,
    ( ~ r1_tarski(sK1,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f40,f53])).

fof(f53,plain,(
    sK1 = k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f52,f45])).

fof(f45,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(resolution,[],[f38,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f37,f21])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

fof(f37,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f34,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f20,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f51,f21])).

fof(f51,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f50,f19])).

fof(f50,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f44,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f44,plain,
    ( v2_tops_1(sK1,sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f43,f36])).

fof(f36,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f35,f21])).

fof(f35,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f33,f19])).

fof(f33,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f20,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f43,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f42,f21])).

fof(f42,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f41,f19])).

fof(f41,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f17,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

fof(f17,plain,
    ( v3_tops_1(sK1,sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f39,f21])).

fof(f39,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f19,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ~ v3_tops_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,
    ( sK1 != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f18,f53])).

fof(f18,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | sK1 != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f48,f21])).

fof(f48,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f47,f19])).

fof(f47,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v3_tops_1(sK1,sK0) ),
    inference(superposition,[],[f28,f36])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:48:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (3784)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (3784)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(global_subsumption,[],[f49,f57,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    v2_tops_1(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f56,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ~r1_tarski(sK1,sK1) | v2_tops_1(sK1,sK0)),
% 0.21/0.49    inference(backward_demodulation,[],[f40,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    sK1 = k2_tops_1(sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f52,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_tops_1(sK0,sK1)),
% 0.21/0.49    inference(resolution,[],[f38,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f37,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f34,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.49    inference(resolution,[],[f20,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    v4_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    sK1 = k2_tops_1(sK0,sK1) | r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f51,f21])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    sK1 = k2_tops_1(sK0,sK1) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f50,f19])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    sK1 = k2_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f44,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v2_tops_1(sK1,sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f43,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f35,f21])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f33,f19])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.49    inference(resolution,[],[f20,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    sK1 = k2_tops_1(sK0,sK1) | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f42,f21])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    sK1 = k2_tops_1(sK0,sK1) | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f41,f19])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    sK1 = k2_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f17,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    v3_tops_1(sK1,sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f39,f21])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f19,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ~v3_tops_1(sK1,sK0)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    sK1 != sK1 | ~v3_tops_1(sK1,sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f18,f53])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ~v3_tops_1(sK1,sK0) | sK1 != k2_tops_1(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ~v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f48,f21])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tops_1(sK1,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f47,f19])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_tops_1(sK1,sK0)),
% 0.21/0.50    inference(superposition,[],[f28,f36])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_tops_1(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_tops_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (3784)------------------------------
% 0.21/0.50  % (3784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3784)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (3784)Memory used [KB]: 6140
% 0.21/0.50  % (3784)Time elapsed: 0.040 s
% 0.21/0.50  % (3784)------------------------------
% 0.21/0.50  % (3784)------------------------------
% 0.21/0.50  % (3777)Success in time 0.133 s
%------------------------------------------------------------------------------
