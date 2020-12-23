%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 (1232 expanded)
%              Number of leaves         :    8 ( 237 expanded)
%              Depth                    :   15
%              Number of atoms          :  279 (7871 expanded)
%              Number of equality atoms :   17 (  83 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f423,plain,(
    $false ),
    inference(global_subsumption,[],[f308,f416,f422,f324])).

fof(f324,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | sK1 = sK2(sK0,sK1)
    | ~ v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(resolution,[],[f194,f288])).

fof(f288,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) ),
    inference(resolution,[],[f286,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f286,plain,(
    r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f23,f124,f169,f121])).

fof(f121,plain,
    ( v3_tex_2(sK1,sK0)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f30,f104])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f26,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f169,plain,(
    ~ v3_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f30,f161,f24,f108])).

fof(f108,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f26,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f161,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(global_subsumption,[],[f25,f27,f28,f29,f30,f110])).

fof(f110,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f26,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f29,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f124,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(global_subsumption,[],[f25,f27,f28,f29,f30,f109])).

fof(f109,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f26,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,
    ( v1_zfmisc_1(sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f194,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | sK1 = X1
      | ~ v1_zfmisc_1(X1) ) ),
    inference(resolution,[],[f57,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK1,X3)
      | ~ v1_zfmisc_1(X3)
      | v1_xboole_0(X3)
      | sK1 = X3 ) ),
    inference(resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f422,plain,(
    v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f421])).

fof(f421,plain,(
    v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f420])).

fof(f420,plain,(
    v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f266,f416])).

fof(f266,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f27,f28,f29,f30,f23,f119,f124,f169,f260])).

fof(f260,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(resolution,[],[f259,f39])).

fof(f259,plain,(
    v2_tex_2(sK2(sK0,sK1),sK0) ),
    inference(global_subsumption,[],[f23,f124,f169,f120])).

fof(f120,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f30,f103])).

fof(f103,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v2_tex_2(sK2(sK0,sK1),sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(sK2(X0,X1),X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f119,plain,
    ( v3_tex_2(sK1,sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f30,f102])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f416,plain,(
    ~ v1_xboole_0(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f293,f413])).

fof(f413,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | ~ v1_xboole_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f407,f333])).

fof(f333,plain,(
    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f23,f124,f169,f119])).

% (26458)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f407,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,sK1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f115,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f115,plain,(
    ! [X5] :
      ( r2_hidden(sK4(u1_struct_0(sK0),X5,sK1),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X5,sK1) ) ),
    inference(resolution,[],[f26,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f293,plain,(
    ~ r1_tarski(sK2(sK0,sK1),sK1) ),
    inference(global_subsumption,[],[f23,f122,f124,f169,f289])).

fof(f289,plain,
    ( ~ r1_tarski(sK2(sK0,sK1),sK1)
    | sK1 = sK2(sK0,sK1) ),
    inference(resolution,[],[f286,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f122,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f30,f105])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f26,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | sK2(X0,X1) != X1
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f308,plain,(
    sK1 != sK2(sK0,sK1) ),
    inference(global_subsumption,[],[f23,f124,f169,f122])).

% (26452)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:08:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (26447)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (26463)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (26454)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (26459)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.50  % (26463)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (26444)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (26446)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f423,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(global_subsumption,[],[f308,f416,f422,f324])).
% 0.20/0.50  fof(f324,plain,(
% 0.20/0.50    v1_xboole_0(sK2(sK0,sK1)) | sK1 = sK2(sK0,sK1) | ~v1_zfmisc_1(sK2(sK0,sK1))),
% 0.20/0.50    inference(resolution,[],[f194,f288])).
% 0.20/0.50  fof(f288,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1)))),
% 0.20/0.50    inference(resolution,[],[f286,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    r1_tarski(sK1,sK2(sK0,sK1))),
% 0.20/0.50    inference(global_subsumption,[],[f23,f124,f169,f121])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    v3_tex_2(sK1,sK0) | r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.50    inference(global_subsumption,[],[f30,f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0) | r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0)),
% 0.20/0.50    inference(resolution,[],[f26,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | v3_tex_2(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f9])).
% 0.20/0.50  fof(f9,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    ~v3_tex_2(sK1,sK0)),
% 0.20/0.50    inference(global_subsumption,[],[f30,f161,f24,f108])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_tex_2(sK1,sK0) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.50    inference(resolution,[],[f26,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.20/0.50    inference(global_subsumption,[],[f25,f27,f28,f29,f30,f110])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.50    inference(resolution,[],[f26,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    v2_tdlat_3(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1)),
% 0.20/0.50    inference(global_subsumption,[],[f25,f27,f28,f29,f30,f109])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.20/0.50    inference(resolution,[],[f26,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(X1)) | v1_xboole_0(X1) | sK1 = X1 | ~v1_zfmisc_1(X1)) )),
% 0.20/0.50    inference(resolution,[],[f57,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X3] : (~r1_tarski(sK1,X3) | ~v1_zfmisc_1(X3) | v1_xboole_0(X3) | sK1 = X3) )),
% 0.20/0.50    inference(resolution,[],[f25,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.50  fof(f422,plain,(
% 0.20/0.50    v1_zfmisc_1(sK2(sK0,sK1))),
% 0.20/0.50    inference(global_subsumption,[],[f421])).
% 0.20/0.50  fof(f421,plain,(
% 0.20/0.50    v1_zfmisc_1(sK2(sK0,sK1))),
% 0.20/0.50    inference(global_subsumption,[],[f420])).
% 0.20/0.50  fof(f420,plain,(
% 0.20/0.50    v1_zfmisc_1(sK2(sK0,sK1))),
% 0.20/0.50    inference(global_subsumption,[],[f266,f416])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1))),
% 0.20/0.50    inference(global_subsumption,[],[f27,f28,f29,f30,f23,f119,f124,f169,f260])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK2(sK0,sK1)) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,sK1))),
% 0.20/0.50    inference(resolution,[],[f259,f39])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    v2_tex_2(sK2(sK0,sK1),sK0)),
% 0.20/0.50    inference(global_subsumption,[],[f23,f124,f169,f120])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    v2_tex_2(sK2(sK0,sK1),sK0) | v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.51    inference(global_subsumption,[],[f30,f103])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0) | v2_tex_2(sK2(sK0,sK1),sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.51    inference(resolution,[],[f26,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_tex_2(sK2(X0,X1),X0) | v3_tex_2(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    v3_tex_2(sK1,sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.51    inference(global_subsumption,[],[f30,f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0)),
% 0.20/0.51    inference(resolution,[],[f26,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f416,plain,(
% 0.20/0.51    ~v1_xboole_0(sK2(sK0,sK1))),
% 0.20/0.51    inference(global_subsumption,[],[f293,f413])).
% 0.20/0.51  fof(f413,plain,(
% 0.20/0.51    r1_tarski(sK2(sK0,sK1),sK1) | ~v1_xboole_0(sK2(sK0,sK1))),
% 0.20/0.51    inference(resolution,[],[f407,f333])).
% 0.20/0.51  fof(f333,plain,(
% 0.20/0.51    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(global_subsumption,[],[f23,f124,f169,f119])).
% 0.20/0.51  % (26458)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  fof(f407,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,sK1) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(resolution,[],[f115,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X5] : (r2_hidden(sK4(u1_struct_0(sK0),X5,sK1),X5) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X5,sK1)) )),
% 0.20/0.51    inference(resolution,[],[f26,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK4(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.51  fof(f293,plain,(
% 0.20/0.51    ~r1_tarski(sK2(sK0,sK1),sK1)),
% 0.20/0.51    inference(global_subsumption,[],[f23,f122,f124,f169,f289])).
% 0.20/0.51  fof(f289,plain,(
% 0.20/0.51    ~r1_tarski(sK2(sK0,sK1),sK1) | sK1 = sK2(sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f286,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.51    inference(global_subsumption,[],[f30,f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0) | sK1 != sK2(sK0,sK1) | v3_tex_2(sK1,sK0)),
% 0.20/0.51    inference(resolution,[],[f26,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | sK2(X0,X1) != X1 | v3_tex_2(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f308,plain,(
% 0.20/0.51    sK1 != sK2(sK0,sK1)),
% 0.20/0.51    inference(global_subsumption,[],[f23,f124,f169,f122])).
% 0.20/0.51  % (26452)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (26463)------------------------------
% 0.20/0.51  % (26463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26463)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (26443)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (26463)Memory used [KB]: 11001
% 0.20/0.51  % (26463)Time elapsed: 0.090 s
% 0.20/0.51  % (26463)------------------------------
% 0.20/0.51  % (26463)------------------------------
% 0.20/0.51  % (26448)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (26450)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (26443)Refutation not found, incomplete strategy% (26443)------------------------------
% 0.20/0.51  % (26443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26443)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26443)Memory used [KB]: 10618
% 0.20/0.51  % (26443)Time elapsed: 0.105 s
% 0.20/0.51  % (26443)------------------------------
% 0.20/0.51  % (26443)------------------------------
% 0.20/0.51  % (26457)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (26442)Success in time 0.161 s
%------------------------------------------------------------------------------
