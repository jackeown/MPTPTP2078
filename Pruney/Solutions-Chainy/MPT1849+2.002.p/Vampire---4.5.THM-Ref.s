%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:37 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  140 (3021 expanded)
%              Number of leaves         :   16 ( 825 expanded)
%              Depth                    :   28
%              Number of atoms          :  421 (13759 expanded)
%              Number of equality atoms :   87 (3090 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1277,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1276,f54])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_pre_topc(sK1,sK0)
    & ~ v1_tex_2(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & m1_pre_topc(X1,sK0)
          & ~ v1_tex_2(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & m1_pre_topc(X1,sK0)
        & ~ v1_tex_2(X1,sK0) )
   => ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_pre_topc(sK1,sK0)
      & ~ v1_tex_2(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v1_tex_2(X1,X0) )
           => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v1_tex_2(X1,X0) )
           => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
         => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).

fof(f1276,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1275,f319])).

fof(f319,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f318,f240])).

fof(f240,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(backward_demodulation,[],[f227,f239])).

fof(f239,plain,(
    u1_struct_0(sK0) = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f238,f54])).

fof(f238,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f235,f56])).

fof(f56,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f235,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = sK2(sK0,sK1) ),
    inference(resolution,[],[f234,f55])).

fof(f55,plain,(
    ~ v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f234,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | u1_struct_0(X1) = sK2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f232,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f232,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | u1_struct_0(X1) = sK2(X1,X0)
      | v1_subset_1(sK2(X1,X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f71,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f227,plain,(
    u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f226,f54])).

fof(f226,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f223,f56])).

fof(f223,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f72,f55])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f318,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f316,f95])).

fof(f95,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f94,f56])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f65,f54])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f316,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f271,f60])).

fof(f60,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f271,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK1)
      | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f259,f95])).

fof(f259,plain,(
    ! [X2] :
      ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X2,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f67,f240])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f1275,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1271,f765])).

fof(f765,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k1_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f241,f764])).

fof(f764,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f758,f54])).

fof(f758,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f483,f244])).

fof(f244,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),sK0) ),
    inference(backward_demodulation,[],[f121,f240])).

fof(f121,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f118,f54])).

fof(f118,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f69,f56])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f483,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),X3)
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(X3,u1_struct_0(sK0))
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f482,f426])).

fof(f426,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),X3)
      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f67,f416])).

fof(f416,plain,(
    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f414,f252])).

fof(f252,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    inference(backward_demodulation,[],[f191,f240])).

fof(f191,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f189,f95])).

fof(f189,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f161,f60])).

fof(f161,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ),
    inference(resolution,[],[f63,f95])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f414,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f410,f249])).

fof(f249,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),sK1) ),
    inference(backward_demodulation,[],[f133,f240])).

fof(f133,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) ),
    inference(resolution,[],[f120,f95])).

fof(f120,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f69,f60])).

fof(f410,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | u1_struct_0(X0) = u1_struct_0(sK0)
      | ~ m1_pre_topc(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f404,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f95,f65])).

fof(f404,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | u1_struct_0(X0) = u1_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(resolution,[],[f324,f270])).

fof(f270,plain,(
    ! [X0] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f257,f95])).

fof(f257,plain,(
    ! [X0] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f66,f240])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f324,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK0))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | u1_struct_0(X0) = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f258,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

% (14501)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f258,plain,(
    ! [X1] :
      ( r1_tarski(u1_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f66,f240])).

fof(f482,plain,(
    ! [X3] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(X3,u1_struct_0(sK0))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(forward_demodulation,[],[f481,f418])).

fof(f418,plain,(
    u1_struct_0(sK0) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    inference(backward_demodulation,[],[f247,f416])).

fof(f247,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    inference(backward_demodulation,[],[f130,f240])).

fof(f130,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f122,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f58,f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f122,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f121,f94])).

fof(f481,plain,(
    ! [X3] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(X3,u1_struct_0(sK0))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),X3)
      | ~ m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(forward_demodulation,[],[f478,f418])).

fof(f478,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),X3)
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(X3,k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))))
      | ~ m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f87,f243])).

fof(f243,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    inference(backward_demodulation,[],[f115,f240])).

fof(f115,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f112,f54])).

fof(f112,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f68,f56])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k1_pre_topc(X0,k2_struct_0(X2)) = X2
      | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_pre_topc(X0,X1) = X2
      | k2_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f241,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(backward_demodulation,[],[f57,f240])).

fof(f57,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f1271,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(sK0,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f480,f132])).

fof(f132,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0) ),
    inference(resolution,[],[f120,f54])).

fof(f480,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(forward_demodulation,[],[f479,f474])).

fof(f474,plain,(
    u1_struct_0(sK0) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(backward_demodulation,[],[f143,f471])).

fof(f471,plain,(
    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f468,f190])).

fof(f190,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f187,f54])).

fof(f187,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f161,f56])).

fof(f468,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f412,f132])).

fof(f412,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | u1_struct_0(X1) = u1_struct_0(sK0)
      | ~ m1_pre_topc(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f411,f94])).

fof(f411,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK1,X1)
      | u1_struct_0(X1) = u1_struct_0(sK0)
      | ~ m1_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f405,f54])).

fof(f405,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK1,X1)
      | u1_struct_0(X1) = u1_struct_0(sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f324,f66])).

fof(f143,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f137,f93])).

fof(f137,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f132,f94])).

fof(f479,plain,(
    ! [X2] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(X2,u1_struct_0(sK0))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
      | ~ m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(forward_demodulation,[],[f477,f474])).

fof(f477,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(X2,k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
      | ~ m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f87,f175])).

fof(f175,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f173,f137])).

fof(f173,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f167,f68])).

fof(f167,plain,(
    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f166,f54])).

fof(f166,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f160,f60])).

fof(f160,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(resolution,[],[f63,f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (14481)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.47  % (14482)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (14479)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (14494)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (14483)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (14502)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (14495)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.50  % (14486)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (14480)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (14487)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (14485)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (14503)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (14490)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (14497)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (14500)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (14479)Refutation not found, incomplete strategy% (14479)------------------------------
% 0.21/0.51  % (14479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14496)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (14492)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (14489)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.27/0.52  % (14493)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.27/0.52  % (14498)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.27/0.52  % (14479)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (14479)Memory used [KB]: 10618
% 1.27/0.52  % (14479)Time elapsed: 0.096 s
% 1.27/0.52  % (14479)------------------------------
% 1.27/0.52  % (14479)------------------------------
% 1.27/0.53  % (14488)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.27/0.53  % (14484)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.27/0.53  % (14504)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.27/0.53  % (14491)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.27/0.53  % (14484)Refutation not found, incomplete strategy% (14484)------------------------------
% 1.27/0.53  % (14484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (14484)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (14484)Memory used [KB]: 6268
% 1.27/0.53  % (14484)Time elapsed: 0.119 s
% 1.27/0.53  % (14484)------------------------------
% 1.27/0.53  % (14484)------------------------------
% 1.37/0.54  % (14499)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.37/0.54  % (14492)Refutation not found, incomplete strategy% (14492)------------------------------
% 1.37/0.54  % (14492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (14492)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (14492)Memory used [KB]: 6396
% 1.37/0.54  % (14492)Time elapsed: 0.132 s
% 1.37/0.54  % (14492)------------------------------
% 1.37/0.54  % (14492)------------------------------
% 1.37/0.54  % (14482)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  fof(f1277,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(subsumption_resolution,[],[f1276,f54])).
% 1.37/0.54  fof(f54,plain,(
% 1.37/0.54    l1_pre_topc(sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f44])).
% 1.37/0.54  fof(f44,plain,(
% 1.37/0.54    (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(sK1,sK0) & ~v1_tex_2(sK1,sK0)) & l1_pre_topc(sK0)),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f43,f42])).
% 1.37/0.54  fof(f42,plain,(
% 1.37/0.54    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_pre_topc(X1,sK0) & ~v1_tex_2(X1,sK0)) & l1_pre_topc(sK0))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f43,plain,(
% 1.37/0.54    ? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_pre_topc(X1,sK0) & ~v1_tex_2(X1,sK0)) => (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(sK1,sK0) & ~v1_tex_2(sK1,sK0))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f22,plain,(
% 1.37/0.54    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) & l1_pre_topc(X0))),
% 1.37/0.54    inference(flattening,[],[f21])).
% 1.37/0.54  fof(f21,plain,(
% 1.37/0.54    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & (m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0))) & l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f20])).
% 1.37/0.54  fof(f20,plain,(
% 1.37/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 1.37/0.54    inference(pure_predicate_removal,[],[f19])).
% 1.37/0.54  fof(f19,negated_conjecture,(
% 1.37/0.54    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 1.37/0.54    inference(negated_conjecture,[],[f18])).
% 1.37/0.54  fof(f18,conjecture,(
% 1.37/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).
% 1.37/0.54  fof(f1276,plain,(
% 1.37/0.54    ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(subsumption_resolution,[],[f1275,f319])).
% 1.37/0.54  fof(f319,plain,(
% 1.37/0.54    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.54    inference(forward_demodulation,[],[f318,f240])).
% 1.37/0.54  fof(f240,plain,(
% 1.37/0.54    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 1.37/0.54    inference(backward_demodulation,[],[f227,f239])).
% 1.37/0.54  fof(f239,plain,(
% 1.37/0.54    u1_struct_0(sK0) = sK2(sK0,sK1)),
% 1.37/0.54    inference(subsumption_resolution,[],[f238,f54])).
% 1.37/0.54  fof(f238,plain,(
% 1.37/0.54    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = sK2(sK0,sK1)),
% 1.37/0.54    inference(subsumption_resolution,[],[f235,f56])).
% 1.37/0.54  fof(f56,plain,(
% 1.37/0.54    m1_pre_topc(sK1,sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f44])).
% 1.37/0.54  fof(f235,plain,(
% 1.37/0.54    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = sK2(sK0,sK1)),
% 1.37/0.54    inference(resolution,[],[f234,f55])).
% 1.37/0.54  fof(f55,plain,(
% 1.37/0.54    ~v1_tex_2(sK1,sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f44])).
% 1.37/0.54  fof(f234,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v1_tex_2(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | u1_struct_0(X1) = sK2(X1,X0)) )),
% 1.37/0.54    inference(subsumption_resolution,[],[f232,f73])).
% 1.37/0.54  fof(f73,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f49])).
% 1.37/0.54  fof(f49,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).
% 1.37/0.54  fof(f48,plain,(
% 1.37/0.54    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f47,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(rectify,[],[f46])).
% 1.37/0.54  fof(f46,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(nnf_transformation,[],[f35])).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(flattening,[],[f34])).
% 1.37/0.54  fof(f34,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f16])).
% 1.37/0.54  fof(f16,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 1.37/0.54  fof(f232,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v1_tex_2(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | u1_struct_0(X1) = sK2(X1,X0) | v1_subset_1(sK2(X1,X0),u1_struct_0(X1))) )),
% 1.37/0.54    inference(resolution,[],[f71,f78])).
% 1.37/0.54  fof(f78,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f51])).
% 1.37/0.54  fof(f51,plain,(
% 1.37/0.54    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.54    inference(nnf_transformation,[],[f39])).
% 1.37/0.54  fof(f39,plain,(
% 1.37/0.54    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f17])).
% 1.37/0.54  fof(f17,axiom,(
% 1.37/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.37/0.54  fof(f71,plain,(
% 1.37/0.54    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f49])).
% 1.37/0.54  fof(f227,plain,(
% 1.37/0.54    u1_struct_0(sK1) = sK2(sK0,sK1)),
% 1.37/0.54    inference(subsumption_resolution,[],[f226,f54])).
% 1.37/0.54  fof(f226,plain,(
% 1.37/0.54    u1_struct_0(sK1) = sK2(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(subsumption_resolution,[],[f223,f56])).
% 1.37/0.54  fof(f223,plain,(
% 1.37/0.54    u1_struct_0(sK1) = sK2(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(resolution,[],[f72,f55])).
% 1.37/0.54  fof(f72,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f49])).
% 1.37/0.54  fof(f318,plain,(
% 1.37/0.54    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.54    inference(subsumption_resolution,[],[f316,f95])).
% 1.37/0.54  fof(f95,plain,(
% 1.37/0.54    l1_pre_topc(sK1)),
% 1.37/0.54    inference(resolution,[],[f94,f56])).
% 1.37/0.54  fof(f94,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.37/0.54    inference(resolution,[],[f65,f54])).
% 1.37/0.54  fof(f65,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f30])).
% 1.37/0.54  fof(f30,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f7])).
% 1.37/0.54  fof(f7,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.37/0.54  fof(f316,plain,(
% 1.37/0.54    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK1)),
% 1.37/0.54    inference(resolution,[],[f271,f60])).
% 1.37/0.54  fof(f60,plain,(
% 1.37/0.54    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f25])).
% 1.37/0.54  fof(f25,plain,(
% 1.37/0.54    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f14])).
% 1.37/0.54  fof(f14,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.37/0.54  fof(f271,plain,(
% 1.37/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK1) | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.37/0.54    inference(subsumption_resolution,[],[f259,f95])).
% 1.37/0.54  fof(f259,plain,(
% 1.37/0.54    ( ! [X2] : (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X2,sK1) | ~l1_pre_topc(sK1)) )),
% 1.37/0.54    inference(superposition,[],[f67,f240])).
% 1.37/0.54  fof(f67,plain,(
% 1.37/0.54    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f32])).
% 1.37/0.54  fof(f32,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f13])).
% 1.37/0.54  fof(f13,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.37/0.54  fof(f1275,plain,(
% 1.37/0.54    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(subsumption_resolution,[],[f1271,f765])).
% 1.37/0.54  fof(f765,plain,(
% 1.37/0.54    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k1_pre_topc(sK0,u1_struct_0(sK0))),
% 1.37/0.54    inference(backward_demodulation,[],[f241,f764])).
% 1.37/0.54  fof(f764,plain,(
% 1.37/0.54    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK0,u1_struct_0(sK0))),
% 1.37/0.54    inference(subsumption_resolution,[],[f758,f54])).
% 1.37/0.54  fof(f758,plain,(
% 1.37/0.54    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(sK0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(resolution,[],[f483,f244])).
% 1.37/0.54  fof(f244,plain,(
% 1.37/0.54    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),sK0)),
% 1.37/0.54    inference(backward_demodulation,[],[f121,f240])).
% 1.37/0.54  fof(f121,plain,(
% 1.37/0.54    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)),
% 1.37/0.54    inference(subsumption_resolution,[],[f118,f54])).
% 1.37/0.54  fof(f118,plain,(
% 1.37/0.54    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(resolution,[],[f69,f56])).
% 1.37/0.54  fof(f69,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f33])).
% 1.37/0.54  fof(f33,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f12])).
% 1.37/0.54  fof(f12,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 1.37/0.54  fof(f483,plain,(
% 1.37/0.54    ( ! [X3] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),X3) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(X3,u1_struct_0(sK0)) | ~l1_pre_topc(X3)) )),
% 1.37/0.54    inference(subsumption_resolution,[],[f482,f426])).
% 1.37/0.54  fof(f426,plain,(
% 1.37/0.54    ( ! [X3] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),X3) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) )),
% 1.37/0.54    inference(superposition,[],[f67,f416])).
% 1.37/0.54  fof(f416,plain,(
% 1.37/0.54    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),
% 1.37/0.54    inference(subsumption_resolution,[],[f414,f252])).
% 1.37/0.54  fof(f252,plain,(
% 1.37/0.54    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),
% 1.37/0.54    inference(backward_demodulation,[],[f191,f240])).
% 1.37/0.54  fof(f191,plain,(
% 1.37/0.54    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.37/0.54    inference(subsumption_resolution,[],[f189,f95])).
% 1.37/0.54  fof(f189,plain,(
% 1.37/0.54    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f188])).
% 1.37/0.54  fof(f188,plain,(
% 1.37/0.54    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)),
% 1.37/0.54    inference(resolution,[],[f161,f60])).
% 1.37/0.54  fof(f161,plain,(
% 1.37/0.54    ( ! [X1] : (~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) )),
% 1.37/0.54    inference(resolution,[],[f63,f95])).
% 1.37/0.54  fof(f63,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f45])).
% 1.37/0.54  fof(f45,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(nnf_transformation,[],[f29])).
% 1.37/0.54  fof(f29,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f11])).
% 1.37/0.54  fof(f11,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.37/0.54  fof(f414,plain,(
% 1.37/0.54    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) | ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),
% 1.37/0.54    inference(resolution,[],[f410,f249])).
% 1.37/0.54  fof(f249,plain,(
% 1.37/0.54    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),sK1)),
% 1.37/0.54    inference(backward_demodulation,[],[f133,f240])).
% 1.37/0.54  fof(f133,plain,(
% 1.37/0.54    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)),
% 1.37/0.54    inference(resolution,[],[f120,f95])).
% 1.37/0.54  fof(f120,plain,(
% 1.37/0.54    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0)) )),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f119])).
% 1.37/0.54  fof(f119,plain,(
% 1.37/0.54    ( ! [X0] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(resolution,[],[f69,f60])).
% 1.37/0.54  fof(f410,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK1) | u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(sK1,X0)) )),
% 1.37/0.54    inference(subsumption_resolution,[],[f404,f97])).
% 1.37/0.54  fof(f97,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK1) | l1_pre_topc(X0)) )),
% 1.37/0.54    inference(resolution,[],[f95,f65])).
% 1.37/0.54  fof(f404,plain,(
% 1.37/0.54    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | u1_struct_0(X0) = u1_struct_0(sK0) | ~m1_pre_topc(X0,sK1)) )),
% 1.37/0.54    inference(resolution,[],[f324,f270])).
% 1.37/0.54  fof(f270,plain,(
% 1.37/0.54    ( ! [X0] : (r1_tarski(u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_pre_topc(X0,sK1)) )),
% 1.37/0.54    inference(subsumption_resolution,[],[f257,f95])).
% 1.37/0.54  fof(f257,plain,(
% 1.37/0.54    ( ! [X0] : (r1_tarski(u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1)) )),
% 1.37/0.54    inference(superposition,[],[f66,f240])).
% 1.37/0.54  fof(f66,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f31])).
% 1.37/0.54  fof(f31,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f15])).
% 1.37/0.54  fof(f15,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 1.37/0.54  fof(f324,plain,(
% 1.37/0.54    ( ! [X0] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(sK0)) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | u1_struct_0(X0) = u1_struct_0(sK0)) )),
% 1.37/0.54    inference(resolution,[],[f258,f85])).
% 1.37/0.54  fof(f85,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.37/0.54    inference(cnf_transformation,[],[f53])).
% 1.37/0.54  fof(f53,plain,(
% 1.37/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.54    inference(flattening,[],[f52])).
% 1.37/0.54  % (14501)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.37/0.54  fof(f52,plain,(
% 1.37/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.54    inference(nnf_transformation,[],[f1])).
% 1.37/0.54  fof(f1,axiom,(
% 1.37/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.54  fof(f258,plain,(
% 1.37/0.54    ( ! [X1] : (r1_tarski(u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 1.37/0.54    inference(superposition,[],[f66,f240])).
% 1.37/0.54  fof(f482,plain,(
% 1.37/0.54    ( ! [X3] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(X3,u1_struct_0(sK0)) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),X3) | ~l1_pre_topc(X3)) )),
% 1.37/0.54    inference(forward_demodulation,[],[f481,f418])).
% 1.37/0.54  fof(f418,plain,(
% 1.37/0.54    u1_struct_0(sK0) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),
% 1.37/0.54    inference(backward_demodulation,[],[f247,f416])).
% 1.37/0.54  fof(f247,plain,(
% 1.37/0.54    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),
% 1.37/0.54    inference(backward_demodulation,[],[f130,f240])).
% 1.37/0.54  fof(f130,plain,(
% 1.37/0.54    u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.37/0.54    inference(resolution,[],[f122,f93])).
% 1.37/0.54  fof(f93,plain,(
% 1.37/0.54    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.37/0.54    inference(resolution,[],[f58,f59])).
% 1.37/0.54  fof(f59,plain,(
% 1.37/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f24])).
% 1.37/0.54  fof(f24,plain,(
% 1.37/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f6])).
% 1.37/0.54  fof(f6,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.37/0.54  fof(f58,plain,(
% 1.37/0.54    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f23])).
% 1.37/0.54  fof(f23,plain,(
% 1.37/0.54    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f4])).
% 1.37/0.54  fof(f4,axiom,(
% 1.37/0.54    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.37/0.54  fof(f122,plain,(
% 1.37/0.54    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.37/0.54    inference(resolution,[],[f121,f94])).
% 1.37/0.54  fof(f481,plain,(
% 1.37/0.54    ( ! [X3] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(X3,u1_struct_0(sK0)) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),X3) | ~m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) )),
% 1.37/0.54    inference(forward_demodulation,[],[f478,f418])).
% 1.37/0.54  fof(f478,plain,(
% 1.37/0.54    ( ! [X3] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)),X3) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) = k1_pre_topc(X3,k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))) | ~m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) )),
% 1.37/0.54    inference(resolution,[],[f87,f243])).
% 1.37/0.54  fof(f243,plain,(
% 1.37/0.54    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))),
% 1.37/0.54    inference(backward_demodulation,[],[f115,f240])).
% 1.37/0.54  fof(f115,plain,(
% 1.37/0.54    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.37/0.54    inference(subsumption_resolution,[],[f112,f54])).
% 1.37/0.54  fof(f112,plain,(
% 1.37/0.54    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(resolution,[],[f68,f56])).
% 1.37/0.54  fof(f68,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f33])).
% 1.37/0.54  fof(f87,plain,(
% 1.37/0.54    ( ! [X2,X0] : (~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k1_pre_topc(X0,k2_struct_0(X2)) = X2 | ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(equality_resolution,[],[f75])).
% 1.37/0.54  fof(f75,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f50])).
% 1.37/0.54  fof(f50,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(nnf_transformation,[],[f37])).
% 1.37/0.54  fof(f37,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(flattening,[],[f36])).
% 1.37/0.54  fof(f36,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 1.37/0.54  fof(f241,plain,(
% 1.37/0.54    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),
% 1.37/0.54    inference(backward_demodulation,[],[f57,f240])).
% 1.37/0.54  fof(f57,plain,(
% 1.37/0.54    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 1.37/0.54    inference(cnf_transformation,[],[f44])).
% 1.37/0.54  fof(f1271,plain,(
% 1.37/0.54    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(sK0,u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(resolution,[],[f480,f132])).
% 1.37/0.54  fof(f132,plain,(
% 1.37/0.54    m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK0)),
% 1.37/0.54    inference(resolution,[],[f120,f54])).
% 1.37/0.54  fof(f480,plain,(
% 1.37/0.54    ( ! [X2] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(X2,u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.37/0.54    inference(forward_demodulation,[],[f479,f474])).
% 1.37/0.54  fof(f474,plain,(
% 1.37/0.54    u1_struct_0(sK0) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.54    inference(backward_demodulation,[],[f143,f471])).
% 1.37/0.54  fof(f471,plain,(
% 1.37/0.54    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.54    inference(subsumption_resolution,[],[f468,f190])).
% 1.37/0.54  fof(f190,plain,(
% 1.37/0.54    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.54    inference(subsumption_resolution,[],[f187,f54])).
% 1.37/0.54  fof(f187,plain,(
% 1.37/0.54    ~l1_pre_topc(sK0) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.54    inference(resolution,[],[f161,f56])).
% 1.37/0.54  fof(f468,plain,(
% 1.37/0.54    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.54    inference(resolution,[],[f412,f132])).
% 1.37/0.54  fof(f412,plain,(
% 1.37/0.54    ( ! [X1] : (~m1_pre_topc(X1,sK0) | u1_struct_0(X1) = u1_struct_0(sK0) | ~m1_pre_topc(sK1,X1)) )),
% 1.37/0.54    inference(subsumption_resolution,[],[f411,f94])).
% 1.37/0.54  fof(f411,plain,(
% 1.37/0.54    ( ! [X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(sK1,X1) | u1_struct_0(X1) = u1_struct_0(sK0) | ~m1_pre_topc(X1,sK0)) )),
% 1.37/0.54    inference(subsumption_resolution,[],[f405,f54])).
% 1.37/0.54  fof(f405,plain,(
% 1.37/0.54    ( ! [X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(sK1,X1) | u1_struct_0(X1) = u1_struct_0(sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0)) )),
% 1.37/0.54    inference(resolution,[],[f324,f66])).
% 1.37/0.54  fof(f143,plain,(
% 1.37/0.54    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.54    inference(resolution,[],[f137,f93])).
% 1.37/0.54  fof(f137,plain,(
% 1.37/0.54    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.54    inference(resolution,[],[f132,f94])).
% 1.37/0.54  fof(f479,plain,(
% 1.37/0.54    ( ! [X2] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(X2,u1_struct_0(sK0)) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.37/0.54    inference(forward_demodulation,[],[f477,f474])).
% 1.37/0.54  fof(f477,plain,(
% 1.37/0.54    ( ! [X2] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k1_pre_topc(X2,k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~m1_subset_1(k2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.37/0.54    inference(resolution,[],[f87,f175])).
% 1.37/0.54  fof(f175,plain,(
% 1.37/0.54    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.54    inference(subsumption_resolution,[],[f173,f137])).
% 1.37/0.54  fof(f173,plain,(
% 1.37/0.54    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.54    inference(resolution,[],[f167,f68])).
% 1.37/0.54  fof(f167,plain,(
% 1.37/0.54    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.54    inference(subsumption_resolution,[],[f166,f54])).
% 1.37/0.54  fof(f166,plain,(
% 1.37/0.54    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f165])).
% 1.37/0.54  fof(f165,plain,(
% 1.37/0.54    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(resolution,[],[f160,f60])).
% 1.37/0.54  fof(f160,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 1.37/0.54    inference(resolution,[],[f63,f54])).
% 1.37/0.54  % SZS output end Proof for theBenchmark
% 1.37/0.54  % (14482)------------------------------
% 1.37/0.54  % (14482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (14482)Termination reason: Refutation
% 1.37/0.54  
% 1.37/0.54  % (14482)Memory used [KB]: 6524
% 1.37/0.54  % (14482)Time elapsed: 0.146 s
% 1.37/0.54  % (14482)------------------------------
% 1.37/0.54  % (14482)------------------------------
% 1.37/0.54  % (14478)Success in time 0.182 s
%------------------------------------------------------------------------------
