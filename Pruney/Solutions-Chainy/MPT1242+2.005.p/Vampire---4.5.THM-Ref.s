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
% DateTime   : Thu Dec  3 13:11:20 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   47 (  92 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   17
%              Number of atoms          :  150 ( 395 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(subsumption_resolution,[],[f134,f21])).

fof(f21,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X1,X2)
                    & v3_pre_topc(X1,X0) )
                 => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f134,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f131,f22])).

fof(f22,plain,(
    ~ r1_tarski(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f131,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f123,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f123,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,k1_tops_1(sK0,X1))
      | ~ r1_tarski(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f122,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f122,plain,(
    ! [X1] :
      ( r1_tarski(sK1,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f119,plain,(
    ! [X1] :
      ( r1_tarski(sK1,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f30,f110])).

fof(f110,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f105,f34])).

fof(f34,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f32,f23])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f105,plain,(
    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f75,f104])).

fof(f104,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f103,f20])).

fof(f20,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f103,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f100,f24])).

fof(f100,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f96,f23])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(resolution,[],[f40,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0)
      | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

% (5824)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f75,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f72,f24])).

fof(f72,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : run_vampire %s %d
% 0.09/0.29  % Computer   : n025.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 10:47:50 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.14/0.38  % (5832)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.14/0.38  % (5833)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.14/0.38  % (5820)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.14/0.39  % (5833)Refutation found. Thanks to Tanya!
% 0.14/0.39  % SZS status Theorem for theBenchmark
% 0.14/0.39  % (5825)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.14/0.39  % SZS output start Proof for theBenchmark
% 0.14/0.39  fof(f135,plain,(
% 0.14/0.39    $false),
% 0.14/0.39    inference(subsumption_resolution,[],[f134,f21])).
% 0.14/0.39  fof(f21,plain,(
% 0.14/0.39    r1_tarski(sK1,sK2)),
% 0.14/0.39    inference(cnf_transformation,[],[f10])).
% 0.14/0.39  fof(f10,plain,(
% 0.14/0.39    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,k1_tops_1(X0,X2)) & r1_tarski(X1,X2) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.14/0.39    inference(flattening,[],[f9])).
% 0.14/0.39  fof(f9,plain,(
% 0.14/0.39    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,k1_tops_1(X0,X2)) & (r1_tarski(X1,X2) & v3_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.14/0.39    inference(ennf_transformation,[],[f8])).
% 0.14/0.39  fof(f8,negated_conjecture,(
% 0.14/0.39    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.14/0.39    inference(negated_conjecture,[],[f7])).
% 0.14/0.39  fof(f7,conjecture,(
% 0.14/0.39    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.14/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.14/0.39  fof(f134,plain,(
% 0.14/0.39    ~r1_tarski(sK1,sK2)),
% 0.14/0.39    inference(subsumption_resolution,[],[f131,f22])).
% 0.14/0.39  fof(f22,plain,(
% 0.14/0.39    ~r1_tarski(sK1,k1_tops_1(sK0,sK2))),
% 0.14/0.39    inference(cnf_transformation,[],[f10])).
% 0.14/0.39  fof(f131,plain,(
% 0.14/0.39    r1_tarski(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(sK1,sK2)),
% 0.14/0.39    inference(resolution,[],[f123,f19])).
% 0.14/0.39  fof(f19,plain,(
% 0.14/0.39    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.39    inference(cnf_transformation,[],[f10])).
% 0.14/0.39  fof(f123,plain,(
% 0.14/0.39    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,X1)) | ~r1_tarski(sK1,X1)) )),
% 0.14/0.39    inference(subsumption_resolution,[],[f122,f24])).
% 0.14/0.39  fof(f24,plain,(
% 0.14/0.39    l1_pre_topc(sK0)),
% 0.14/0.39    inference(cnf_transformation,[],[f10])).
% 0.14/0.39  fof(f122,plain,(
% 0.14/0.39    ( ! [X1] : (r1_tarski(sK1,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X1) | ~l1_pre_topc(sK0)) )),
% 0.14/0.39    inference(subsumption_resolution,[],[f119,f23])).
% 0.14/0.39  fof(f23,plain,(
% 0.14/0.39    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.39    inference(cnf_transformation,[],[f10])).
% 0.14/0.39  fof(f119,plain,(
% 0.14/0.39    ( ! [X1] : (r1_tarski(sK1,k1_tops_1(sK0,X1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X1) | ~l1_pre_topc(sK0)) )),
% 0.14/0.39    inference(superposition,[],[f30,f110])).
% 0.14/0.39  fof(f110,plain,(
% 0.14/0.39    sK1 = k1_tops_1(sK0,sK1)),
% 0.14/0.39    inference(forward_demodulation,[],[f105,f34])).
% 0.14/0.39  fof(f34,plain,(
% 0.14/0.39    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.14/0.39    inference(resolution,[],[f32,f23])).
% 0.14/0.39  fof(f32,plain,(
% 0.14/0.39    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.14/0.39    inference(cnf_transformation,[],[f18])).
% 0.14/0.39  fof(f18,plain,(
% 0.14/0.39    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.14/0.39    inference(ennf_transformation,[],[f2])).
% 0.14/0.39  fof(f2,axiom,(
% 0.14/0.39    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.14/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.14/0.39  fof(f105,plain,(
% 0.14/0.39    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1)),
% 0.14/0.39    inference(backward_demodulation,[],[f75,f104])).
% 0.14/0.39  fof(f104,plain,(
% 0.14/0.39    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.14/0.39    inference(subsumption_resolution,[],[f103,f20])).
% 0.14/0.39  fof(f20,plain,(
% 0.14/0.39    v3_pre_topc(sK1,sK0)),
% 0.14/0.39    inference(cnf_transformation,[],[f10])).
% 0.14/0.39  fof(f103,plain,(
% 0.14/0.39    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~v3_pre_topc(sK1,sK0)),
% 0.14/0.39    inference(subsumption_resolution,[],[f100,f24])).
% 0.14/0.39  fof(f100,plain,(
% 0.14/0.39    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v3_pre_topc(sK1,sK0)),
% 0.14/0.39    inference(resolution,[],[f96,f23])).
% 0.14/0.39  fof(f96,plain,(
% 0.14/0.39    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.14/0.39    inference(duplicate_literal_removal,[],[f91])).
% 0.14/0.39  fof(f91,plain,(
% 0.14/0.39    ( ! [X0,X1] : (~l1_pre_topc(X0) | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.14/0.39    inference(resolution,[],[f40,f29])).
% 0.14/0.39  fof(f29,plain,(
% 0.14/0.39    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.14/0.39    inference(cnf_transformation,[],[f14])).
% 0.14/0.39  fof(f14,plain,(
% 0.14/0.39    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.14/0.39    inference(ennf_transformation,[],[f5])).
% 0.14/0.39  fof(f5,axiom,(
% 0.14/0.39    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.14/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 0.14/0.39  fof(f40,plain,(
% 0.14/0.39    ( ! [X0,X1] : (~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0) | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.14/0.39    inference(resolution,[],[f27,f31])).
% 0.14/0.39  fof(f31,plain,(
% 0.14/0.39    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.14/0.39    inference(cnf_transformation,[],[f17])).
% 0.14/0.39  fof(f17,plain,(
% 0.14/0.39    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.14/0.39    inference(ennf_transformation,[],[f1])).
% 0.14/0.39  % (5824)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.14/0.39  fof(f1,axiom,(
% 0.14/0.39    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.14/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.14/0.39  fof(f27,plain,(
% 0.14/0.39    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.14/0.39    inference(cnf_transformation,[],[f13])).
% 0.14/0.39  fof(f13,plain,(
% 0.14/0.39    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.14/0.39    inference(flattening,[],[f12])).
% 0.14/0.39  fof(f12,plain,(
% 0.14/0.39    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.14/0.39    inference(ennf_transformation,[],[f3])).
% 0.14/0.39  fof(f3,axiom,(
% 0.14/0.39    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.14/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.14/0.39  fof(f75,plain,(
% 0.14/0.39    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.14/0.39    inference(subsumption_resolution,[],[f72,f24])).
% 0.14/0.39  fof(f72,plain,(
% 0.14/0.39    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.14/0.39    inference(resolution,[],[f25,f23])).
% 0.14/0.39  fof(f25,plain,(
% 0.14/0.39    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.14/0.39    inference(cnf_transformation,[],[f11])).
% 0.14/0.39  fof(f11,plain,(
% 0.14/0.39    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.14/0.39    inference(ennf_transformation,[],[f4])).
% 0.14/0.39  fof(f4,axiom,(
% 0.14/0.39    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.14/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.14/0.39  fof(f30,plain,(
% 0.14/0.39    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 0.14/0.39    inference(cnf_transformation,[],[f16])).
% 0.14/0.39  fof(f16,plain,(
% 0.14/0.39    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.14/0.39    inference(flattening,[],[f15])).
% 0.14/0.39  fof(f15,plain,(
% 0.14/0.39    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.14/0.39    inference(ennf_transformation,[],[f6])).
% 0.14/0.39  fof(f6,axiom,(
% 0.14/0.39    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.14/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.14/0.39  % SZS output end Proof for theBenchmark
% 0.14/0.39  % (5833)------------------------------
% 0.14/0.39  % (5833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.39  % (5833)Termination reason: Refutation
% 0.14/0.39  
% 0.14/0.39  % (5833)Memory used [KB]: 6140
% 0.14/0.39  % (5833)Time elapsed: 0.061 s
% 0.14/0.39  % (5833)------------------------------
% 0.14/0.39  % (5833)------------------------------
% 0.14/0.39  % (5817)Success in time 0.09 s
%------------------------------------------------------------------------------
