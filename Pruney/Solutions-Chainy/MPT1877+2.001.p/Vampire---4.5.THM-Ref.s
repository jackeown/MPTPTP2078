%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 877 expanded)
%              Number of leaves         :    8 ( 156 expanded)
%              Depth                    :   31
%              Number of atoms          :  334 (4965 expanded)
%              Number of equality atoms :   47 (1097 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(subsumption_resolution,[],[f330,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v3_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v3_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v3_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tex_2)).

fof(f330,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f329,f114])).

fof(f114,plain,(
    sK2 != sK4(sK1,sK2) ),
    inference(subsumption_resolution,[],[f113,f49])).

fof(f49,plain,(
    ~ v3_tex_2(sK2,sK1) ),
    inference(backward_demodulation,[],[f25,f23])).

fof(f23,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ~ v3_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f113,plain,
    ( sK2 != sK4(sK1,sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f112,f27])).

fof(f27,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK1)
    | sK2 != sK4(sK1,sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f98,f50])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f21,f23])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f98,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | sK2 != sK4(sK1,sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(resolution,[],[f93,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | sK4(X0,X1) != X1
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f93,plain,(
    v2_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f92,f22])).

fof(f22,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f92,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f90,f27])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_tex_2(sK2,sK1) ),
    inference(resolution,[],[f64,f50])).

fof(f64,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | v2_tex_2(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f63,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(sK0)
      | v2_tex_2(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(sK0)
      | v2_tex_2(sK2,X0) ) ),
    inference(resolution,[],[f55,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_tex_2(X3,X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X3,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | X2 != X3
      | ~ v2_tex_2(X2,X0)
      | v2_tex_2(X3,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_tex_2(X3,X1)
                  | ~ v2_tex_2(X2,X0)
                  | X2 != X3
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_tex_2(X3,X1)
                  | ~ v2_tex_2(X2,X0)
                  | X2 != X3
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).

fof(f55,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f54,f28])).

fof(f54,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f53,f26])).

fof(f53,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f24,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    v3_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f329,plain,
    ( sK2 = sK4(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f326,f111])).

fof(f111,plain,(
    r1_tarski(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f110,f49])).

fof(f110,plain,
    ( r1_tarski(sK2,sK4(sK1,sK2))
    | v3_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f109,f27])).

fof(f109,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(sK2,sK4(sK1,sK2))
    | v3_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f97,f50])).

fof(f97,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | r1_tarski(sK2,sK4(sK1,sK2))
    | v3_tex_2(sK2,sK1) ),
    inference(resolution,[],[f93,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,sK4(X0,X1))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f326,plain,
    ( ~ r1_tarski(sK2,sK4(sK1,sK2))
    | sK2 = sK4(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f284,f24])).

fof(f284,plain,(
    ! [X1] :
      ( ~ v3_tex_2(X1,sK0)
      | ~ r1_tarski(X1,sK4(sK1,sK2))
      | sK4(sK1,sK2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f283,f28])).

fof(f283,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(X1,sK4(sK1,sK2))
      | sK4(sK1,sK2) = X1
      | ~ v3_tex_2(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f274,f180])).

% (6878)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f180,plain,(
    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f105,f174])).

fof(f174,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f173,f168])).

fof(f168,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f148,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f148,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f146,f28])).

fof(f146,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f144,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f144,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f143,f27])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f139,f28])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f73,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f73,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f72,f22])).

fof(f72,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f70,f27])).

fof(f70,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f51,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f27,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f173,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(resolution,[],[f171,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f171,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f160,f43])).

fof(f160,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f158,f27])).

fof(f158,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f156,f44])).

fof(f156,plain,(
    m1_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f149,f28])).

fof(f149,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f82,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f74,f27])).

fof(f74,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK1) ) ),
    inference(superposition,[],[f40,f22])).

fof(f82,plain,(
    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f80,f28])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f41])).

fof(f52,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f28,f45])).

fof(f105,plain,(
    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f104,f49])).

fof(f104,plain,
    ( m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f103,f27])).

fof(f103,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f95,f50])).

fof(f95,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_tex_2(sK2,sK1) ),
    inference(resolution,[],[f93,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f274,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(X1,sK4(sK1,sK2))
      | sK4(sK1,sK2) = X1
      | ~ v3_tex_2(X1,sK0) ) ),
    inference(resolution,[],[f268,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f268,plain,(
    v2_tex_2(sK4(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f267,f28])).

fof(f267,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(sK4(sK1,sK2),sK0) ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | v2_tex_2(sK4(sK1,sK2),sK0) ),
    inference(resolution,[],[f126,f180])).

fof(f126,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | v2_tex_2(sK4(sK1,sK2),X0) ) ),
    inference(forward_demodulation,[],[f125,f22])).

fof(f125,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | v2_tex_2(sK4(sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f124,f27])).

fof(f124,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | ~ l1_pre_topc(sK1)
      | v2_tex_2(sK4(sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f118,f105])).

fof(f118,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | ~ l1_pre_topc(sK1)
      | v2_tex_2(sK4(sK1,sK2),X0) ) ),
    inference(resolution,[],[f108,f48])).

fof(f108,plain,(
    v2_tex_2(sK4(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f107,f49])).

fof(f107,plain,
    ( v2_tex_2(sK4(sK1,sK2),sK1)
    | v3_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f106,f27])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_tex_2(sK4(sK1,sK2),sK1)
    | v3_tex_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f96,f50])).

fof(f96,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | v2_tex_2(sK4(sK1,sK2),sK1)
    | v3_tex_2(sK2,sK1) ),
    inference(resolution,[],[f93,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(sK4(X0,X1),X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:07:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (6866)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (6863)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (6864)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (6865)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (6873)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (6883)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (6872)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (6866)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (6875)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (6882)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (6881)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (6880)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (6867)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (6886)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (6874)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (6870)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (6861)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (6879)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (6871)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (6862)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (6868)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f331,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f330,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v3_tex_2(X3,X1) & (v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tex_2(X3,X1))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tex_2(X3,X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tex_2)).
% 0.21/0.52  fof(f330,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f329,f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    sK2 != sK4(sK1,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f113,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ~v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(backward_demodulation,[],[f25,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    sK2 = sK3),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ~v3_tex_2(sK3,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    sK2 != sK4(sK1,sK2) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f112,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | sK2 != sK4(sK1,sK2) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f98,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    inference(forward_demodulation,[],[f21,f23])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | sK2 != sK4(sK1,sK2) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f93,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | sK4(X0,X1) != X1 | v3_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    v2_tex_2(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f92,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | v2_tex_2(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f90,f27])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | v2_tex_2(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f64,f50])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v2_tex_2(sK2,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f63,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | v2_tex_2(sK2,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f57,f26])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | v2_tex_2(sK2,X0)) )),
% 0.21/0.52    inference(resolution,[],[f55,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~v2_tex_2(X3,X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X0) | v2_tex_2(X3,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | X2 != X3 | ~v2_tex_2(X2,X0) | v2_tex_2(X3,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v2_tex_2(X3,X1) | ~v2_tex_2(X2,X0) | X2 != X3 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_tex_2(X3,X1) | (~v2_tex_2(X2,X0) | X2 != X3 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    v2_tex_2(sK2,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f54,f28])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    v2_tex_2(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f53,f26])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f24,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    v3_tex_2(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    sK2 = sK4(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f326,f111])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    r1_tarski(sK2,sK4(sK1,sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f110,f49])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    r1_tarski(sK2,sK4(sK1,sK2)) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f109,f27])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | r1_tarski(sK2,sK4(sK1,sK2)) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f97,f50])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | r1_tarski(sK2,sK4(sK1,sK2)) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f93,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,sK4(X0,X1)) | v3_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f326,plain,(
% 0.21/0.52    ~r1_tarski(sK2,sK4(sK1,sK2)) | sK2 = sK4(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(resolution,[],[f284,f24])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    ( ! [X1] : (~v3_tex_2(X1,sK0) | ~r1_tarski(X1,sK4(sK1,sK2)) | sK4(sK1,sK2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f283,f28])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X1,sK4(sK1,sK2)) | sK4(sK1,sK2) = X1 | ~v3_tex_2(X1,sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f274,f180])).
% 0.21/0.52  % (6878)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(backward_demodulation,[],[f105,f174])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f173,f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.52    inference(resolution,[],[f148,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f146,f28])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(resolution,[],[f144,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f143,f27])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f139,f28])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f73,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    inference(forward_demodulation,[],[f72,f22])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f70,f27])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f51,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK1)),
% 0.21/0.52    inference(resolution,[],[f27,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.21/0.52    inference(resolution,[],[f171,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    inference(resolution,[],[f160,f43])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f158,f27])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    inference(resolution,[],[f156,f44])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    m1_pre_topc(sK0,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f149,f28])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,sK1)),
% 0.21/0.52    inference(resolution,[],[f82,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f74,f27])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK1)) )),
% 0.21/0.52    inference(superposition,[],[f40,f22])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f80,f28])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f52,f41])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    m1_pre_topc(sK0,sK0)),
% 0.21/0.52    inference(resolution,[],[f28,f45])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f104,f49])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f103,f27])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f95,f50])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f93,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X1,sK4(sK1,sK2)) | sK4(sK1,sK2) = X1 | ~v3_tex_2(X1,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f268,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v2_tex_2(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | X1 = X2 | ~v3_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    v2_tex_2(sK4(sK1,sK2),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f267,f28])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | v2_tex_2(sK4(sK1,sK2),sK0)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f265])).
% 0.21/0.52  fof(f265,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v2_tex_2(sK4(sK1,sK2),sK0)),
% 0.21/0.52    inference(resolution,[],[f126,f180])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v2_tex_2(sK4(sK1,sK2),X0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f125,f22])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | v2_tex_2(sK4(sK1,sK2),X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f124,f27])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | v2_tex_2(sK4(sK1,sK2),X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f118,f105])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | v2_tex_2(sK4(sK1,sK2),X0)) )),
% 0.21/0.52    inference(resolution,[],[f108,f48])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    v2_tex_2(sK4(sK1,sK2),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f49])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    v2_tex_2(sK4(sK1,sK2),sK1) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f27])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | v2_tex_2(sK4(sK1,sK2),sK1) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f96,f50])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | v2_tex_2(sK4(sK1,sK2),sK1) | v3_tex_2(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f93,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tex_2(sK4(X0,X1),X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (6866)------------------------------
% 0.21/0.52  % (6866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6866)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (6866)Memory used [KB]: 6268
% 0.21/0.52  % (6866)Time elapsed: 0.091 s
% 0.21/0.52  % (6866)------------------------------
% 0.21/0.52  % (6866)------------------------------
% 0.21/0.52  % (6859)Success in time 0.163 s
%------------------------------------------------------------------------------
