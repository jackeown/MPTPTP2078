%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1452+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  178 (2986 expanded)
%              Number of leaves         :    5 ( 515 expanded)
%              Depth                    :   41
%              Number of atoms          :  952 (36930 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f356,plain,(
    $false ),
    inference(subsumption_resolution,[],[f355,f281])).

fof(f281,plain,(
    v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f280,f263])).

fof(f263,plain,
    ( v17_lattices(sK1)
    | v15_lattices(sK1) ),
    inference(subsumption_resolution,[],[f262,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <~> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <~> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ( ( l3_lattices(X1)
                & v17_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v17_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) )
            <=> ( l3_lattices(k7_filter_1(X0,X1))
                & v17_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_filter_1)).

fof(f262,plain,
    ( v17_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK1) ),
    inference(subsumption_resolution,[],[f261,f52])).

fof(f52,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f261,plain,
    ( v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK1) ),
    inference(subsumption_resolution,[],[f260,f51])).

fof(f51,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f260,plain,
    ( v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK1) ),
    inference(subsumption_resolution,[],[f259,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f259,plain,
    ( v17_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK1) ),
    inference(subsumption_resolution,[],[f258,f55])).

fof(f55,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f258,plain,
    ( v17_lattices(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK1) ),
    inference(subsumption_resolution,[],[f249,f54])).

fof(f54,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f249,plain,
    ( v17_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK1) ),
    inference(resolution,[],[f245,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ sP4(X1,X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v15_lattices(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_filter_1)).

fof(f245,plain,
    ( sP4(sK1,sK0)
    | v17_lattices(sK1) ),
    inference(resolution,[],[f244,f48])).

fof(f48,plain,
    ( sP2(sK1,sK0)
    | v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f244,plain,(
    ! [X6,X7] :
      ( ~ sP2(X7,X6)
      | sP4(X7,X6) ) ),
    inference(subsumption_resolution,[],[f243,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f243,plain,(
    ! [X6,X7] :
      ( ~ l3_lattices(k7_filter_1(X6,X7))
      | sP4(X7,X6)
      | ~ sP2(X7,X6) ) ),
    inference(subsumption_resolution,[],[f242,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( v16_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f153,f40])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f150,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f150,plain,(
    ! [X0,X1] :
      ( v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(resolution,[],[f59,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v17_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v16_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

fof(f242,plain,(
    ! [X6,X7] :
      ( ~ v16_lattices(k7_filter_1(X6,X7))
      | ~ l3_lattices(k7_filter_1(X6,X7))
      | sP4(X7,X6)
      | ~ sP2(X7,X6) ) ),
    inference(subsumption_resolution,[],[f241,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( v15_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f147,f40])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(k7_filter_1(X0,X1))
      | v15_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f144,f37])).

fof(f144,plain,(
    ! [X0,X1] :
      ( v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v15_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(resolution,[],[f58,f39])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v15_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f241,plain,(
    ! [X6,X7] :
      ( ~ v15_lattices(k7_filter_1(X6,X7))
      | ~ v16_lattices(k7_filter_1(X6,X7))
      | ~ l3_lattices(k7_filter_1(X6,X7))
      | sP4(X7,X6)
      | ~ sP2(X7,X6) ) ),
    inference(subsumption_resolution,[],[f236,f37])).

fof(f236,plain,(
    ! [X6,X7] :
      ( v2_struct_0(k7_filter_1(X6,X7))
      | ~ v15_lattices(k7_filter_1(X6,X7))
      | ~ v16_lattices(k7_filter_1(X6,X7))
      | ~ l3_lattices(k7_filter_1(X6,X7))
      | sP4(X7,X6)
      | ~ sP2(X7,X6) ) ),
    inference(resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f280,plain,
    ( v17_lattices(sK1)
    | ~ v15_lattices(sK1) ),
    inference(subsumption_resolution,[],[f279,f202])).

fof(f202,plain,
    ( v11_lattices(sK1)
    | v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f201,f53])).

fof(f201,plain,
    ( v17_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK1) ),
    inference(subsumption_resolution,[],[f200,f52])).

fof(f200,plain,
    ( v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK1) ),
    inference(subsumption_resolution,[],[f199,f51])).

fof(f199,plain,
    ( v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK1) ),
    inference(subsumption_resolution,[],[f198,f50])).

fof(f198,plain,
    ( v17_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK1) ),
    inference(subsumption_resolution,[],[f197,f55])).

fof(f197,plain,
    ( v17_lattices(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK1) ),
    inference(subsumption_resolution,[],[f195,f54])).

fof(f195,plain,
    ( v17_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK1) ),
    inference(resolution,[],[f193,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ sP3(X1,X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v11_lattices(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_filter_1)).

fof(f193,plain,
    ( sP3(sK1,sK0)
    | v17_lattices(sK1) ),
    inference(resolution,[],[f192,f48])).

fof(f192,plain,(
    ! [X6,X7] :
      ( ~ sP2(X7,X6)
      | sP3(X7,X6) ) ),
    inference(subsumption_resolution,[],[f191,f40])).

fof(f191,plain,(
    ! [X6,X7] :
      ( ~ l3_lattices(k7_filter_1(X6,X7))
      | sP3(X7,X6)
      | ~ sP2(X7,X6) ) ),
    inference(subsumption_resolution,[],[f190,f142])).

% (20139)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f142,plain,(
    ! [X0,X1] :
      ( v11_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f141,f40])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f138,f37])).

fof(f138,plain,(
    ! [X0,X1] :
      ( v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(k7_filter_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(resolution,[],[f57,f39])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v11_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f190,plain,(
    ! [X6,X7] :
      ( ~ v11_lattices(k7_filter_1(X6,X7))
      | ~ l3_lattices(k7_filter_1(X6,X7))
      | sP3(X7,X6)
      | ~ sP2(X7,X6) ) ),
    inference(subsumption_resolution,[],[f185,f37])).

fof(f185,plain,(
    ! [X6,X7] :
      ( v2_struct_0(k7_filter_1(X6,X7))
      | ~ v11_lattices(k7_filter_1(X6,X7))
      | ~ l3_lattices(k7_filter_1(X6,X7))
      | sP3(X7,X6)
      | ~ sP2(X7,X6) ) ),
    inference(resolution,[],[f60,f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | sP3(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f279,plain,
    ( v17_lattices(sK1)
    | ~ v11_lattices(sK1)
    | ~ v15_lattices(sK1) ),
    inference(subsumption_resolution,[],[f278,f52])).

fof(f278,plain,
    ( v17_lattices(sK1)
    | ~ v11_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f277,f50])).

fof(f277,plain,
    ( v17_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v11_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(duplicate_literal_removal,[],[f276])).

fof(f276,plain,
    ( v17_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v11_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v17_lattices(sK1) ),
    inference(resolution,[],[f257,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v16_lattices(X0)
      | v2_struct_0(X0)
      | ~ v11_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ l3_lattices(X0)
      | v17_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v17_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_lattices)).

fof(f257,plain,
    ( v16_lattices(sK1)
    | v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f256,f53])).

fof(f256,plain,
    ( v17_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK1) ),
    inference(subsumption_resolution,[],[f255,f52])).

fof(f255,plain,
    ( v17_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK1) ),
    inference(subsumption_resolution,[],[f254,f51])).

fof(f254,plain,
    ( v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK1) ),
    inference(subsumption_resolution,[],[f253,f50])).

fof(f253,plain,
    ( v17_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK1) ),
    inference(subsumption_resolution,[],[f252,f55])).

fof(f252,plain,
    ( v17_lattices(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK1) ),
    inference(subsumption_resolution,[],[f248,f54])).

fof(f248,plain,
    ( v17_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK1) ),
    inference(resolution,[],[f245,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ sP4(X1,X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v16_lattices(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f355,plain,(
    ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f354,f314])).

fof(f314,plain,(
    v17_lattices(sK0) ),
    inference(subsumption_resolution,[],[f313,f308])).

fof(f308,plain,
    ( v17_lattices(sK0)
    | v15_lattices(sK0) ),
    inference(subsumption_resolution,[],[f307,f53])).

fof(f307,plain,
    ( v17_lattices(sK0)
    | v2_struct_0(sK0)
    | v15_lattices(sK0) ),
    inference(subsumption_resolution,[],[f306,f52])).

fof(f306,plain,
    ( v17_lattices(sK0)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK0) ),
    inference(subsumption_resolution,[],[f305,f51])).

fof(f305,plain,
    ( v17_lattices(sK0)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK0) ),
    inference(subsumption_resolution,[],[f304,f50])).

fof(f304,plain,
    ( v17_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK0) ),
    inference(subsumption_resolution,[],[f303,f55])).

fof(f303,plain,
    ( v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK0) ),
    inference(subsumption_resolution,[],[f296,f54])).

fof(f296,plain,
    ( v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v15_lattices(sK0) ),
    inference(resolution,[],[f246,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ sP4(X1,X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v15_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f246,plain,
    ( sP4(sK1,sK0)
    | v17_lattices(sK0) ),
    inference(resolution,[],[f244,f44])).

fof(f44,plain,
    ( sP2(sK1,sK0)
    | v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f313,plain,
    ( v17_lattices(sK0)
    | ~ v15_lattices(sK0) ),
    inference(subsumption_resolution,[],[f312,f222])).

fof(f222,plain,
    ( v11_lattices(sK0)
    | v17_lattices(sK0) ),
    inference(subsumption_resolution,[],[f221,f53])).

fof(f221,plain,
    ( v17_lattices(sK0)
    | v2_struct_0(sK0)
    | v11_lattices(sK0) ),
    inference(subsumption_resolution,[],[f220,f52])).

fof(f220,plain,
    ( v17_lattices(sK0)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK0) ),
    inference(subsumption_resolution,[],[f219,f51])).

fof(f219,plain,
    ( v17_lattices(sK0)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK0) ),
    inference(subsumption_resolution,[],[f218,f50])).

fof(f218,plain,
    ( v17_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK0) ),
    inference(subsumption_resolution,[],[f217,f55])).

fof(f217,plain,
    ( v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK0) ),
    inference(subsumption_resolution,[],[f210,f54])).

fof(f210,plain,
    ( v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v11_lattices(sK0) ),
    inference(resolution,[],[f194,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ sP3(X1,X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v11_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f194,plain,
    ( sP3(sK1,sK0)
    | v17_lattices(sK0) ),
    inference(resolution,[],[f192,f44])).

fof(f312,plain,
    ( v17_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v15_lattices(sK0) ),
    inference(subsumption_resolution,[],[f311,f55])).

fof(f311,plain,
    ( v17_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f310,f53])).

fof(f310,plain,
    ( v17_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,
    ( v17_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v17_lattices(sK0) ),
    inference(resolution,[],[f302,f56])).

fof(f302,plain,
    ( v16_lattices(sK0)
    | v17_lattices(sK0) ),
    inference(subsumption_resolution,[],[f301,f53])).

fof(f301,plain,
    ( v17_lattices(sK0)
    | v2_struct_0(sK0)
    | v16_lattices(sK0) ),
    inference(subsumption_resolution,[],[f300,f52])).

fof(f300,plain,
    ( v17_lattices(sK0)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK0) ),
    inference(subsumption_resolution,[],[f299,f51])).

fof(f299,plain,
    ( v17_lattices(sK0)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK0) ),
    inference(subsumption_resolution,[],[f298,f50])).

fof(f298,plain,
    ( v17_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK0) ),
    inference(subsumption_resolution,[],[f297,f55])).

fof(f297,plain,
    ( v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK0) ),
    inference(subsumption_resolution,[],[f295,f54])).

fof(f295,plain,
    ( v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK0)
    | v16_lattices(sK0) ),
    inference(resolution,[],[f246,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ sP4(X1,X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X0)
      | v16_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f354,plain,
    ( ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f353,f290])).

fof(f290,plain,(
    v11_lattices(sK1) ),
    inference(subsumption_resolution,[],[f289,f52])).

fof(f289,plain,
    ( ~ l3_lattices(sK1)
    | v11_lattices(sK1) ),
    inference(subsumption_resolution,[],[f284,f50])).

fof(f284,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | v11_lattices(sK1) ),
    inference(resolution,[],[f281,f57])).

fof(f353,plain,
    ( ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f352,f323])).

fof(f323,plain,(
    v11_lattices(sK0) ),
    inference(subsumption_resolution,[],[f322,f55])).

fof(f322,plain,
    ( ~ l3_lattices(sK0)
    | v11_lattices(sK0) ),
    inference(subsumption_resolution,[],[f317,f53])).

fof(f317,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v11_lattices(sK0) ),
    inference(resolution,[],[f314,f57])).

fof(f352,plain,
    ( ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f351,f53])).

fof(f351,plain,
    ( v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f350,f54])).

fof(f350,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f349,f52])).

fof(f349,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f348,f286])).

fof(f286,plain,(
    v16_lattices(sK1) ),
    inference(subsumption_resolution,[],[f285,f52])).

fof(f285,plain,
    ( ~ l3_lattices(sK1)
    | v16_lattices(sK1) ),
    inference(subsumption_resolution,[],[f282,f50])).

fof(f282,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | v16_lattices(sK1) ),
    inference(resolution,[],[f281,f59])).

fof(f348,plain,
    ( ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f347,f288])).

fof(f288,plain,(
    v15_lattices(sK1) ),
    inference(subsumption_resolution,[],[f287,f52])).

fof(f287,plain,
    ( ~ l3_lattices(sK1)
    | v15_lattices(sK1) ),
    inference(subsumption_resolution,[],[f283,f50])).

fof(f283,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | v15_lattices(sK1) ),
    inference(resolution,[],[f281,f58])).

fof(f347,plain,
    ( ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f346,f51])).

fof(f346,plain,
    ( ~ v10_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f345,f50])).

fof(f345,plain,
    ( v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f344,f55])).

fof(f344,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f343,f319])).

fof(f319,plain,(
    v16_lattices(sK0) ),
    inference(subsumption_resolution,[],[f318,f55])).

fof(f318,plain,
    ( ~ l3_lattices(sK0)
    | v16_lattices(sK0) ),
    inference(subsumption_resolution,[],[f315,f53])).

fof(f315,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v16_lattices(sK0) ),
    inference(resolution,[],[f314,f59])).

fof(f343,plain,
    ( ~ v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f340,f321])).

fof(f321,plain,(
    v15_lattices(sK0) ),
    inference(subsumption_resolution,[],[f320,f55])).

fof(f320,plain,
    ( ~ l3_lattices(sK0)
    | v15_lattices(sK0) ),
    inference(subsumption_resolution,[],[f316,f53])).

fof(f316,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v15_lattices(sK0) ),
    inference(resolution,[],[f314,f58])).

fof(f340,plain,
    ( ~ v15_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v11_lattices(sK0)
    | ~ v11_lattices(sK1)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(resolution,[],[f339,f134])).

fof(f134,plain,
    ( ~ sP2(sK1,sK0)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1) ),
    inference(subsumption_resolution,[],[f133,f52])).

fof(f133,plain,
    ( ~ sP2(sK1,sK0)
    | ~ v17_lattices(sK0)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f132,f51])).

fof(f132,plain,
    ( ~ sP2(sK1,sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f131,f50])).

fof(f131,plain,
    ( ~ sP2(sK1,sK0)
    | ~ v17_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f130,f55])).

fof(f130,plain,
    ( ~ sP2(sK1,sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f129,f54])).

fof(f129,plain,
    ( ~ sP2(sK1,sK0)
    | ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f41,f53])).

fof(f41,plain,
    ( ~ sP2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f339,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ v15_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v11_lattices(X0)
      | ~ v11_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1)
      | sP2(X1,X0)
      | v2_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f327,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f327,plain,(
    ! [X0,X1] :
      ( ~ sP3(X1,X0)
      | ~ v10_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1)
      | sP2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f74,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | sP2(X0,X1)
      | ~ sP3(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ sP4(X0,X1)
      | ~ sP4(X0,X1)
      | ~ sP3(X0,X1) ) ),
    inference(resolution,[],[f173,f162])).

fof(f162,plain,(
    ! [X2,X3] :
      ( v17_lattices(k7_filter_1(X2,X3))
      | ~ sP4(X3,X2)
      | ~ sP3(X3,X2) ) ),
    inference(resolution,[],[f160,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v11_lattices(k7_filter_1(X0,X1))
      | ~ sP3(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f160,plain,(
    ! [X2,X3] :
      ( ~ v11_lattices(k7_filter_1(X2,X3))
      | v17_lattices(k7_filter_1(X2,X3))
      | ~ sP4(X3,X2) ) ),
    inference(subsumption_resolution,[],[f159,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f159,plain,(
    ! [X2,X3] :
      ( ~ v11_lattices(k7_filter_1(X2,X3))
      | ~ l3_lattices(k7_filter_1(X2,X3))
      | v17_lattices(k7_filter_1(X2,X3))
      | ~ sP4(X3,X2) ) ),
    inference(subsumption_resolution,[],[f158,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v15_lattices(k7_filter_1(X0,X1))
      | ~ sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f158,plain,(
    ! [X2,X3] :
      ( ~ v11_lattices(k7_filter_1(X2,X3))
      | ~ v15_lattices(k7_filter_1(X2,X3))
      | ~ l3_lattices(k7_filter_1(X2,X3))
      | v17_lattices(k7_filter_1(X2,X3))
      | ~ sP4(X3,X2) ) ),
    inference(subsumption_resolution,[],[f156,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f156,plain,(
    ! [X2,X3] :
      ( v2_struct_0(k7_filter_1(X2,X3))
      | ~ v11_lattices(k7_filter_1(X2,X3))
      | ~ v15_lattices(k7_filter_1(X2,X3))
      | ~ l3_lattices(k7_filter_1(X2,X3))
      | v17_lattices(k7_filter_1(X2,X3))
      | ~ sP4(X3,X2) ) ),
    inference(resolution,[],[f56,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v16_lattices(k7_filter_1(X0,X1))
      | ~ sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f173,plain,(
    ! [X2,X3] :
      ( ~ v17_lattices(k7_filter_1(X2,X3))
      | sP2(X3,X2)
      | ~ sP4(X3,X2) ) ),
    inference(subsumption_resolution,[],[f172,f73])).

fof(f172,plain,(
    ! [X2,X3] :
      ( ~ v17_lattices(k7_filter_1(X2,X3))
      | ~ l3_lattices(k7_filter_1(X2,X3))
      | sP2(X3,X2)
      | ~ sP4(X3,X2) ) ),
    inference(subsumption_resolution,[],[f167,f69])).

fof(f167,plain,(
    ! [X2,X3] :
      ( v2_struct_0(k7_filter_1(X2,X3))
      | ~ v17_lattices(k7_filter_1(X2,X3))
      | ~ l3_lattices(k7_filter_1(X2,X3))
      | sP2(X3,X2)
      | ~ sP4(X3,X2) ) ),
    inference(resolution,[],[f36,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ v17_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
