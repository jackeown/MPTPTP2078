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
% DateTime   : Thu Dec  3 13:17:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 491 expanded)
%              Number of leaves         :    9 ( 100 expanded)
%              Depth                    :   26
%              Number of atoms          :  200 (3207 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(global_subsumption,[],[f21,f96,f102])).

fof(f102,plain,(
    r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f101,f52])).

fof(f52,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f46,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f46,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f101,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f98,f51])).

fof(f51,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f48,f34])).

fof(f48,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f44,f31])).

fof(f44,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f98,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1) ),
    inference(resolution,[],[f96,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f96,plain,(
    r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f95,f52])).

fof(f95,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f94,f24])).

fof(f24,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f92,f51])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,sK3) ) ),
    inference(resolution,[],[f88,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f88,plain,(
    ! [X0] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3))
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f87,f50])).

fof(f50,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f47,f31])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X0] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3))
      | ~ l1_pre_topc(sK2)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(resolution,[],[f80,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f36,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK2))
      | r1_xboole_0(X0,u1_struct_0(sK3)) ) ),
    inference(superposition,[],[f42,f74])).

fof(f74,plain,(
    u1_struct_0(sK3) = k4_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f73,f53])).

fof(f53,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f50,f34])).

fof(f73,plain,
    ( ~ l1_struct_0(sK2)
    | u1_struct_0(sK3) = k4_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f70,f51])).

fof(f70,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | u1_struct_0(sK3) = k4_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f67,f62])).

fof(f62,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f61,f53])).

fof(f61,plain,
    ( ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f60,f51])).

fof(f60,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2) ),
    inference(resolution,[],[f59,f37])).

fof(f59,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f58,f51])).

fof(f58,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f57,f53])).

fof(f57,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f37,f20])).

fof(f20,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ r1_tsep_1(X3,X2)
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X2)
      | u1_struct_0(X3) = k4_xboole_0(u1_struct_0(X3),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f21,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (6623)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.46  % (6616)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.46  % (6616)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(global_subsumption,[],[f21,f96,f102])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    r1_tsep_1(sK3,sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f101,f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    l1_struct_0(sK1)),
% 0.21/0.46    inference(resolution,[],[f49,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    l1_pre_topc(sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f46,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.46    inference(negated_conjecture,[],[f9])).
% 0.21/0.46  fof(f9,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.21/0.46    inference(resolution,[],[f35,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    m1_pre_topc(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f98,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    l1_struct_0(sK3)),
% 0.21/0.46    inference(resolution,[],[f48,f34])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    l1_pre_topc(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f44,f31])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.21/0.46    inference(resolution,[],[f35,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    m1_pre_topc(sK3,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1)),
% 0.21/0.46    inference(resolution,[],[f96,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    r1_tsep_1(sK1,sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f95,f52])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    ~l1_struct_0(sK1) | r1_tsep_1(sK1,sK3)),
% 0.21/0.46    inference(resolution,[],[f94,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    m1_pre_topc(sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~l1_struct_0(X0) | r1_tsep_1(X0,sK3)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f92,f51])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~l1_struct_0(sK3) | ~l1_struct_0(X0) | r1_tsep_1(X0,sK3)) )),
% 0.21/0.46    inference(resolution,[],[f88,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK2)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f87,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    l1_pre_topc(sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f47,f31])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.21/0.46    inference(resolution,[],[f35,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    m1_pre_topc(sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X0,sK2)) )),
% 0.21/0.46    inference(resolution,[],[f80,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.46    inference(resolution,[],[f36,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | r1_xboole_0(X0,u1_struct_0(sK3))) )),
% 0.21/0.46    inference(superposition,[],[f42,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    u1_struct_0(sK3) = k4_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.21/0.46    inference(subsumption_resolution,[],[f73,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    l1_struct_0(sK2)),
% 0.21/0.46    inference(resolution,[],[f50,f34])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ~l1_struct_0(sK2) | u1_struct_0(sK3) = k4_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.21/0.46    inference(subsumption_resolution,[],[f70,f51])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | u1_struct_0(sK3) = k4_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.21/0.46    inference(resolution,[],[f67,f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    r1_tsep_1(sK3,sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f61,f53])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f60,f51])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2)),
% 0.21/0.46    inference(resolution,[],[f59,f37])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    r1_tsep_1(sK2,sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f58,f51])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f57,f53])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3) | r1_tsep_1(sK2,sK3)),
% 0.21/0.46    inference(resolution,[],[f37,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X2,X3] : (~r1_tsep_1(X3,X2) | ~l1_struct_0(X3) | ~l1_struct_0(X2) | u1_struct_0(X3) = k4_xboole_0(u1_struct_0(X3),u1_struct_0(X2))) )),
% 0.21/0.46    inference(resolution,[],[f33,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (6616)------------------------------
% 0.21/0.46  % (6616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (6616)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (6616)Memory used [KB]: 6140
% 0.21/0.46  % (6616)Time elapsed: 0.059 s
% 0.21/0.46  % (6616)------------------------------
% 0.21/0.46  % (6616)------------------------------
% 0.21/0.47  % (6602)Success in time 0.11 s
%------------------------------------------------------------------------------
