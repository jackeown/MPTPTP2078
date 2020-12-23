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
% DateTime   : Thu Dec  3 13:21:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 133 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  173 ( 438 expanded)
%              Number of equality atoms :   37 (  47 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(subsumption_resolution,[],[f187,f59])).

fof(f59,plain,(
    ~ v2_tex_2(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f33,f56])).

fof(f56,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f33,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f187,plain,(
    v2_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f186,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f186,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f185,f170])).

fof(f170,plain,(
    k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    inference(resolution,[],[f125,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f125,plain,(
    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f124,f59])).

fof(f124,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK0) ),
    inference(resolution,[],[f73,f35])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f185,plain,
    ( k1_xboole_0 != sK2(sK0,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f184,f65])).

fof(f65,plain,(
    v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f64,f35])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f184,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | k1_xboole_0 != sK2(sK0,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0) ),
    inference(superposition,[],[f137,f72])).

fof(f72,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f55,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f41,f35])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f137,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X1)
      | k1_xboole_0 != sK2(X1,k1_xboole_0)
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f109,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f38,f36])).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != sK2(X0,k1_xboole_0)
      | ~ v3_pre_topc(X1,X0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(backward_demodulation,[],[f83,f104])).

fof(f104,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f61,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f48,f50])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_xboole_0) != sK2(X0,k1_xboole_0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f81,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X1,k1_xboole_0) = k9_subset_1(X0,k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f68,f66])).

fof(f66,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f52,f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f68,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,k1_xboole_0) = k9_subset_1(X0,k1_xboole_0,X1) ),
    inference(resolution,[],[f53,f37])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,X1)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f42,f37])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (12577)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.42  % (12577)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f188,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f187,f59])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    ~v2_tex_2(k1_xboole_0,sK0)),
% 0.20/0.42    inference(backward_demodulation,[],[f33,f56])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    k1_xboole_0 = sK1),
% 0.20/0.42    inference(resolution,[],[f39,f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    v1_xboole_0(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.42    inference(pure_predicate_removal,[],[f16])).
% 0.20/0.42  fof(f16,negated_conjecture,(
% 0.20/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.42    inference(negated_conjecture,[],[f15])).
% 0.20/0.42  fof(f15,conjecture,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ~v2_tex_2(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f187,plain,(
% 0.20/0.42    v2_tex_2(k1_xboole_0,sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f186,f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    l1_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f186,plain,(
% 0.20/0.42    ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f185,f170])).
% 0.20/0.42  fof(f170,plain,(
% 0.20/0.42    k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.20/0.42    inference(resolution,[],[f125,f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.42  fof(f125,plain,(
% 0.20/0.42    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f124,f59])).
% 0.20/0.42  fof(f124,plain,(
% 0.20/0.42    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | v2_tex_2(k1_xboole_0,sK0)),
% 0.20/0.42    inference(resolution,[],[f73,f35])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_pre_topc(X0) | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.20/0.42    inference(resolution,[],[f47,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,axiom,(
% 0.20/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 0.20/0.42  fof(f185,plain,(
% 0.20/0.42    k1_xboole_0 != sK2(sK0,k1_xboole_0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f184,f65])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f64,f35])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    ~l1_pre_topc(sK0) | v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.42    inference(resolution,[],[f49,f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    v2_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,axiom,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.20/0.42  fof(f184,plain,(
% 0.20/0.42    ~v3_pre_topc(k2_struct_0(sK0),sK0) | k1_xboole_0 != sK2(sK0,k1_xboole_0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0)),
% 0.20/0.42    inference(superposition,[],[f137,f72])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.42    inference(resolution,[],[f55,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,axiom,(
% 0.20/0.42    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    l1_struct_0(sK0)),
% 0.20/0.42    inference(resolution,[],[f41,f35])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.42  fof(f137,plain,(
% 0.20/0.42    ( ! [X1] : (~v3_pre_topc(u1_struct_0(X1),X1) | k1_xboole_0 != sK2(X1,k1_xboole_0) | ~l1_pre_topc(X1) | v2_tex_2(k1_xboole_0,X1)) )),
% 0.20/0.42    inference(resolution,[],[f109,f54])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(forward_demodulation,[],[f38,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.42  fof(f109,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 != sK2(X0,k1_xboole_0) | ~v3_pre_topc(X1,X0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.20/0.42    inference(backward_demodulation,[],[f83,f104])).
% 0.20/0.42  fof(f104,plain,(
% 0.20/0.42    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.20/0.42    inference(superposition,[],[f61,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.43    inference(resolution,[],[f48,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X1,k1_xboole_0) != sK2(X0,k1_xboole_0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f81,f70])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X1,k1_xboole_0) = k9_subset_1(X0,k1_xboole_0,X1)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f68,f66])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.20/0.43    inference(resolution,[],[f52,f37])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k9_subset_1(X0,X1,k1_xboole_0) = k9_subset_1(X0,k1_xboole_0,X1)) )),
% 0.20/0.43    inference(resolution,[],[f53,f37])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,X1) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.20/0.43    inference(resolution,[],[f42,f37])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (12577)------------------------------
% 0.20/0.43  % (12577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (12577)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (12577)Memory used [KB]: 1791
% 0.20/0.43  % (12577)Time elapsed: 0.032 s
% 0.20/0.43  % (12577)------------------------------
% 0.20/0.43  % (12577)------------------------------
% 0.20/0.43  % (12559)Success in time 0.073 s
%------------------------------------------------------------------------------
