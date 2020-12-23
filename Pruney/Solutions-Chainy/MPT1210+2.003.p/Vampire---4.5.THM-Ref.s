%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 243 expanded)
%              Number of leaves         :    7 (  43 expanded)
%              Depth                    :   29
%              Number of atoms          :  287 (1193 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f101,f24])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,X1,k6_lattices(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,X1,k6_lattices(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r3_lattices(X0,X1,k6_lattices(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,X1,k6_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattices)).

fof(f101,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f42])).

fof(f42,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f29,f27])).

fof(f27,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f100,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f99,f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f99,plain,(
    ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f98,f23])).

fof(f23,plain,(
    ~ r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f98,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f97,f24])).

fof(f97,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f96,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f96,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f95,f27])).

fof(f95,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f94,f60])).

fof(f60,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f59,f27])).

fof(f59,plain,
    ( ~ l3_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f58,f24])).

fof(f58,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(resolution,[],[f35,f25])).

fof(f25,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f94,plain,
    ( ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f93,f57])).

fof(f57,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f56,f27])).

fof(f56,plain,
    ( ~ l3_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f55,f24])).

fof(f55,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(resolution,[],[f34,f25])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f89,f51])).

fof(f51,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f50,f27])).

fof(f50,plain,
    ( ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f49,f24])).

fof(f49,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(resolution,[],[f32,f25])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f89,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f39,f87])).

fof(f87,plain,(
    r1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f86,f24])).

fof(f86,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f80,f36])).

fof(f80,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f79,f24])).

fof(f79,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f78,f22])).

fof(f78,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f77,f27])).

fof(f77,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f76,f57])).

fof(f76,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f73,f51])).

fof(f73,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f38,f67])).

fof(f67,plain,(
    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f66,f24])).

fof(f66,plain,
    ( v2_struct_0(sK0)
    | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f65,f27])).

fof(f65,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f64,f26])).

fof(f26,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,
    ( ~ v14_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f61,f25])).

fof(f61,plain,
    ( ~ v10_lattices(sK0)
    | ~ v14_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(resolution,[],[f37,f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (24580)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.48  % (24588)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.49  % (24580)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f101,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~r3_lattices(X0,X1,k6_lattices(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~r3_lattices(X0,X1,k6_lattices(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r3_lattices(X0,X1,k6_lattices(X0))))),
% 0.20/0.49    inference(negated_conjecture,[],[f7])).
% 0.20/0.49  fof(f7,conjecture,(
% 0.20/0.49    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r3_lattices(X0,X1,k6_lattices(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattices)).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f100,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    l2_lattices(sK0)),
% 0.20/0.49    inference(resolution,[],[f29,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    l3_lattices(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f99,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f98,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ~r3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f97,f24])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f96,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f95,f27])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f94,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    v9_lattices(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f59,f27])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ~l3_lattices(sK0) | v9_lattices(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f58,f24])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    v2_struct_0(sK0) | ~l3_lattices(sK0) | v9_lattices(sK0)),
% 0.20/0.49    inference(resolution,[],[f35,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    v10_lattices(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v9_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f93,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    v8_lattices(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f56,f27])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ~l3_lattices(sK0) | v8_lattices(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f55,f24])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    v2_struct_0(sK0) | ~l3_lattices(sK0) | v8_lattices(sK0)),
% 0.20/0.49    inference(resolution,[],[f34,f25])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v8_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f89,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    v6_lattices(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f50,f27])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f49,f24])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    v2_struct_0(sK0) | ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.20/0.49    inference(resolution,[],[f32,f25])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v6_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.20/0.49    inference(resolution,[],[f39,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    r1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f86,f24])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    r1_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f85,f42])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f80,f36])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f79,f24])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f78,f22])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f77,f27])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~l3_lattices(sK0) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f76,f57])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~v8_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f73,f51])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.49    inference(superposition,[],[f38,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f66,f24])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    v2_struct_0(sK0) | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f65,f27])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f64,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    v14_lattices(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ~v14_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f61,f25])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ~v10_lattices(sK0) | ~v14_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.20/0.49    inference(resolution,[],[f37,f22])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0) | ~v14_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k4_lattices(X0,k6_lattices(X0),X1) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_lattices(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (24580)------------------------------
% 0.20/0.49  % (24580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (24580)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (24580)Memory used [KB]: 6140
% 0.20/0.49  % (24580)Time elapsed: 0.067 s
% 0.20/0.49  % (24580)------------------------------
% 0.20/0.49  % (24580)------------------------------
% 0.20/0.50  % (24566)Success in time 0.137 s
%------------------------------------------------------------------------------
