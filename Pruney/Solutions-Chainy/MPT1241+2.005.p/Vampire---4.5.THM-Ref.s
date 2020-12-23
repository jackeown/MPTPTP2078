%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 236 expanded)
%              Number of leaves         :    7 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  165 (1313 expanded)
%              Number of equality atoms :   43 ( 303 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(global_subsumption,[],[f20,f130,f153])).

fof(f153,plain,(
    sK3 = k1_tops_1(sK1,sK3) ),
    inference(forward_demodulation,[],[f147,f36])).

fof(f36,plain,(
    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f34,f23])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( k1_tops_1(X0,X2) = X2
                       => v3_pre_topc(X2,X0) )
                      & ( v3_pre_topc(X3,X1)
                       => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f147,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(backward_demodulation,[],[f85,f146])).

fof(f146,plain,(
    k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f140,f118])).

fof(f118,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(subsumption_resolution,[],[f115,f25])).

fof(f25,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f115,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ l1_pre_topc(sK1)
    | ~ v3_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f112,f23])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

% (9673)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0)
      | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f30,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

% (9680)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f30,plain,(
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

fof(f140,plain,(
    v3_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f130,f22])).

fof(f22,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) ),
    inference(subsumption_resolution,[],[f82,f25])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) ),
    inference(resolution,[],[f28,f23])).

fof(f28,plain,(
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

fof(f130,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(backward_demodulation,[],[f46,f129])).

fof(f129,plain,(
    sK2 = k1_tops_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f128,f19])).

fof(f19,plain,
    ( sK3 != k1_tops_1(sK1,sK3)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f128,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(forward_demodulation,[],[f125,f36])).

fof(f125,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(superposition,[],[f85,f120])).

fof(f120,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(resolution,[],[f118,f21])).

fof(f21,plain,
    ( v3_pre_topc(sK3,sK1)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f45,f26])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f42,f27])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f35,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f20,plain,
    ( sK3 != k1_tops_1(sK1,sK3)
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (9683)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.47  % (9683)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (9674)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.48  % (9691)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(global_subsumption,[],[f20,f130,f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.48    inference(forward_demodulation,[],[f147,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))),
% 0.21/0.48    inference(resolution,[],[f34,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))),
% 0.21/0.48    inference(backward_demodulation,[],[f85,f146])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))),
% 0.21/0.48    inference(resolution,[],[f140,f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~v3_pre_topc(sK3,sK1) | k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    l1_pre_topc(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) | ~l1_pre_topc(sK1) | ~v3_pre_topc(sK3,sK1)),
% 0.21/0.48    inference(resolution,[],[f112,f23])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f49,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % (9673)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0) | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.48    inference(resolution,[],[f30,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  % (9680)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    v3_pre_topc(sK3,sK1)),
% 0.21/0.48    inference(resolution,[],[f130,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f82,f25])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~l1_pre_topc(sK1) | k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))),
% 0.21/0.48    inference(resolution,[],[f28,f23])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    v3_pre_topc(sK2,sK0)),
% 0.21/0.48    inference(backward_demodulation,[],[f46,f129])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f128,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    sK3 != k1_tops_1(sK1,sK3) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    sK3 = k1_tops_1(sK1,sK3) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.48    inference(forward_demodulation,[],[f125,f36])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.48    inference(superposition,[],[f85,f120])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.48    inference(resolution,[],[f118,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v3_pre_topc(sK3,sK1) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f45,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f42,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.21/0.48    inference(resolution,[],[f35,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    sK3 != k1_tops_1(sK1,sK3) | ~v3_pre_topc(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9683)------------------------------
% 0.21/0.48  % (9683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9683)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9683)Memory used [KB]: 6268
% 0.21/0.48  % (9683)Time elapsed: 0.066 s
% 0.21/0.48  % (9683)------------------------------
% 0.21/0.48  % (9683)------------------------------
% 0.21/0.49  % (9669)Success in time 0.129 s
%------------------------------------------------------------------------------
