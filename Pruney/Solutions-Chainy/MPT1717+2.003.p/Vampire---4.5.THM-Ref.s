%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 105 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :   21
%              Number of atoms          :  226 ( 536 expanded)
%              Number of equality atoms :   26 (  74 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(subsumption_resolution,[],[f58,f18])).

fof(f18,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tmap_1)).

fof(f58,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f57,f19])).

fof(f19,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f54,f20])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f16])).

fof(f16,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f52,f32])).

fof(f32,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f29,f20])).

fof(f29,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f22,f16])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f51,f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f51,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,sK1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f50,f15])).

fof(f15,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(sK1,sK1)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(sK1,sK1)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f46,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X2,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f46,plain,(
    r1_tsep_1(sK1,sK1) ),
    inference(subsumption_resolution,[],[f45,f17])).

fof(f17,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k2_tsep_1(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,
    ( r1_tsep_1(sK1,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f44,f18])).

fof(f44,plain,
    ( r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f43,f19])).

fof(f43,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f42,f15])).

fof(f42,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f39,f20])).

fof(f39,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1) ),
    inference(resolution,[],[f38,f16])).

fof(f38,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X1)
      | r1_tsep_1(X2,X2)
      | v2_struct_0(X1)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X1,X2,X2) ) ),
    inference(subsumption_resolution,[],[f35,f22])).

fof(f35,plain,(
    ! [X2,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | r1_tsep_1(X2,X2)
      | v2_struct_0(X1)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X1,X2,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f34])).

fof(f34,plain,(
    ! [X2,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | r1_tsep_1(X2,X2)
      | v2_struct_0(X1)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X1,X2,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f24,f21])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
             => ( ~ r1_tsep_1(X1,X2)
               => ( ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => m1_pre_topc(X2,X1) )
                  & ( m1_pre_topc(X2,X1)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                  & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                   => m1_pre_topc(X1,X2) )
                  & ( m1_pre_topc(X1,X2)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tsep_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (16911)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.48  % (16927)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.48  % (16926)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.48  % (16919)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.48  % (16915)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.48  % (16910)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.48  % (16919)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f58,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tmap_1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f57,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f54,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f53,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f52,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    l1_pre_topc(sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f29,f20])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.21/0.48    inference(resolution,[],[f22,f16])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK1)) )),
% 0.21/0.48    inference(resolution,[],[f51,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f50,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ~v2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f46,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tsep_1(X2,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    r1_tsep_1(sK1,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f45,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k2_tsep_1(sK0,sK1,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    r1_tsep_1(sK1,sK1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f44,f18])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    r1_tsep_1(sK1,sK1) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f43,f19])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | r1_tsep_1(sK1,sK1) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f42,f15])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    v2_struct_0(sK1) | ~v2_pre_topc(sK0) | r1_tsep_1(sK1,sK1) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f39,f20])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK0) | r1_tsep_1(sK1,sK1) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1)),
% 0.21/0.48    inference(resolution,[],[f38,f16])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X1) | r1_tsep_1(X2,X2) | v2_struct_0(X1) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X1,X2,X2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f35,f22])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | r1_tsep_1(X2,X2) | v2_struct_0(X1) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X1,X2,X2) | ~l1_pre_topc(X2)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | r1_tsep_1(X2,X2) | v2_struct_0(X1) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X1,X2,X2) | ~l1_pre_topc(X2)) )),
% 0.21/0.48    inference(resolution,[],[f24,f21])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(X0) | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X2,X1) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X2,X1) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ((k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => m1_pre_topc(X2,X1)) & (m1_pre_topc(X2,X1) => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tsep_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (16919)------------------------------
% 0.21/0.48  % (16919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16919)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (16919)Memory used [KB]: 6140
% 0.21/0.48  % (16919)Time elapsed: 0.088 s
% 0.21/0.48  % (16919)------------------------------
% 0.21/0.48  % (16919)------------------------------
% 0.21/0.49  % (16905)Success in time 0.128 s
%------------------------------------------------------------------------------
