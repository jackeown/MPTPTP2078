%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1847+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 177 expanded)
%              Number of leaves         :    5 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :  142 ( 754 expanded)
%              Number of equality atoms :   26 ( 136 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(subsumption_resolution,[],[f102,f16])).

fof(f16,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

fof(f102,plain,(
    ~ v1_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f101,f73])).

fof(f73,plain,(
    ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f48,f68])).

fof(f68,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(superposition,[],[f54,f15])).

fof(f15,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | u1_struct_0(sK1) = X0 ) ),
    inference(resolution,[],[f44,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f44,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f40,f19])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f18,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f18,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f47,f17])).

fof(f17,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f46,f19])).

fof(f46,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f45,f14])).

fof(f14,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(sK2,sK0) ),
    inference(superposition,[],[f23,f37])).

fof(f37,plain,(
    u1_struct_0(sK2) = sK3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f36,f17])).

fof(f36,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | v1_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f32,f19])).

fof(f32,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK2) = sK3(sK0,sK2)
    | v1_tex_2(sK2,sK0) ),
    inference(resolution,[],[f14,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f101,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f100,f19])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f99,f18])).

% (9681)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (9674)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f99,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0) ),
    inference(resolution,[],[f71,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f38,f68])).

fof(f38,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f35,f37])).

fof(f35,plain,(
    m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f34,f17])).

fof(f34,plain,
    ( m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f31,f19])).

fof(f31,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(sK2,sK0) ),
    inference(resolution,[],[f14,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
