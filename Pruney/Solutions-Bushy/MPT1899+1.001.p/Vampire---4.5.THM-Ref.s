%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1899+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 (3912 expanded)
%              Number of leaves         :   11 (1239 expanded)
%              Depth                    :   29
%              Number of atoms          :  614 (41756 expanded)
%              Number of equality atoms :   18 ( 168 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f485,plain,(
    $false ),
    inference(subsumption_resolution,[],[f484,f252])).

fof(f252,plain,(
    m1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) ),
    inference(subsumption_resolution,[],[f251,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ! [X2] :
        ( ~ v4_tex_2(X2,sK0)
        | ~ m1_pre_topc(sK1,X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & m1_pre_topc(sK1,sK0)
    & v1_tdlat_3(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ~ v4_tex_2(X2,X0)
                | ~ m1_pre_topc(X1,X2)
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,sK0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,sK0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ v4_tex_2(X2,sK0)
            | ~ m1_pre_topc(X1,X2)
            | ~ m1_pre_topc(X2,sK0)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & v1_tdlat_3(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( ~ v4_tex_2(X2,sK0)
          | ~ m1_pre_topc(sK1,X2)
          | ~ m1_pre_topc(X2,sK0)
          | ~ v1_pre_topc(X2)
          | v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & v1_tdlat_3(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v4_tex_2(X2,X0)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v4_tex_2(X2,X0)
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tex_2)).

fof(f251,plain,
    ( m1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f250,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f250,plain,
    ( m1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f249,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f249,plain,
    ( m1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f248,f237])).

fof(f237,plain,(
    ~ v1_xboole_0(sK2(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f230,f176])).

fof(f176,plain,(
    m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f175,f31])).

fof(f175,plain,
    ( m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f174,f32])).

fof(f174,plain,
    ( m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f173,f33])).

fof(f33,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f173,plain,
    ( m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f172,f34])).

fof(f172,plain,
    ( m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f149])).

fof(f149,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f141,f34])).

fof(f141,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f37,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f37,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f169,plain,
    ( m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f162,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK2(X0,X1),X0)
            & r1_tarski(X1,sK2(X0,X1))
            & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK2(X0,X1),X0)
        & r1_tarski(X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

fof(f162,plain,(
    v2_tex_2(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f161,f31])).

fof(f161,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f160,f34])).

fof(f160,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f159,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f159,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f149])).

fof(f158,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f147,f36])).

fof(f36,plain,(
    v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f147,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ v1_tdlat_3(sK1)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f37,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f230,plain,
    ( ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(sK2(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f186,f88])).

fof(f88,plain,(
    ! [X8] :
      ( ~ v3_tex_2(X8,sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X8) ) ),
    inference(subsumption_resolution,[],[f87,f32])).

fof(f87,plain,(
    ! [X8] :
      ( ~ v3_tex_2(X8,sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X8)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f63,f34])).

fof(f63,plain,(
    ! [X8] :
      ( ~ v3_tex_2(X8,sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f31,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f186,plain,(
    v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f185,f31])).

fof(f185,plain,
    ( v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f184,f32])).

% (7646)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f184,plain,
    ( v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f183,f33])).

fof(f183,plain,
    ( v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f182,f34])).

fof(f182,plain,
    ( v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f171,f149])).

fof(f171,plain,
    ( v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f162,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f248,plain,
    ( m1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f234,f176])).

fof(f234,plain,
    ( m1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f186,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK3(X0,X1),X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK3(X0,X1)) = X1
            & v4_tex_2(sK3(X0,X1),X0)
            & m1_pre_topc(sK3(X0,X1),X0)
            & v1_pre_topc(sK3(X0,X1))
            & ~ v2_struct_0(sK3(X0,X1)) )
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & v4_tex_2(X2,X0)
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK3(X0,X1)) = X1
        & v4_tex_2(sK3(X0,X1),X0)
        & m1_pre_topc(sK3(X0,X1),X0)
        & v1_pre_topc(sK3(X0,X1))
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & v4_tex_2(X2,X0)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & v4_tex_2(X2,X0)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tex_2)).

fof(f484,plain,(
    ~ m1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) ),
    inference(subsumption_resolution,[],[f483,f440])).

fof(f440,plain,(
    ~ m1_pre_topc(sK1,sK3(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f439,f242])).

fof(f242,plain,(
    ~ v2_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f241,f31])).

fof(f241,plain,
    ( ~ v2_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f240,f32])).

fof(f240,plain,
    ( ~ v2_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f239,f34])).

fof(f239,plain,
    ( ~ v2_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f238,f237])).

fof(f238,plain,
    ( ~ v2_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f232,f176])).

fof(f232,plain,
    ( ~ v2_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f186,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f439,plain,
    ( ~ m1_pre_topc(sK1,sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f438,f247])).

fof(f247,plain,(
    v1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f246,f31])).

fof(f246,plain,
    ( v1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f245,f32])).

fof(f245,plain,
    ( v1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f244,f34])).

fof(f244,plain,
    ( v1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f243,f237])).

fof(f243,plain,
    ( v1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f233,f176])).

fof(f233,plain,
    ( v1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f186,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK3(X0,X1))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f438,plain,
    ( ~ m1_pre_topc(sK1,sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ v1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f437,f252])).

fof(f437,plain,
    ( ~ m1_pre_topc(sK1,sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | ~ v1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    inference(resolution,[],[f257,f38])).

fof(f38,plain,(
    ! [X2] :
      ( ~ v4_tex_2(X2,sK0)
      | ~ m1_pre_topc(sK1,X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f257,plain,(
    v4_tex_2(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) ),
    inference(subsumption_resolution,[],[f256,f31])).

fof(f256,plain,
    ( v4_tex_2(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f255,f32])).

fof(f255,plain,
    ( v4_tex_2(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f34])).

fof(f254,plain,
    ( v4_tex_2(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f253,f237])).

fof(f253,plain,
    ( v4_tex_2(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f235,f176])).

fof(f235,plain,
    ( v4_tex_2(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f186,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_tex_2(sK3(X0,X1),X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f483,plain,
    ( m1_pre_topc(sK1,sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) ),
    inference(subsumption_resolution,[],[f481,f181])).

fof(f181,plain,(
    r1_tarski(u1_struct_0(sK1),sK2(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f180,f31])).

fof(f180,plain,
    ( r1_tarski(u1_struct_0(sK1),sK2(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f179,f32])).

fof(f179,plain,
    ( r1_tarski(u1_struct_0(sK1),sK2(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f178,f33])).

fof(f178,plain,
    ( r1_tarski(u1_struct_0(sK1),sK2(sK0,u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f177,f34])).

fof(f177,plain,
    ( r1_tarski(u1_struct_0(sK1),sK2(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f170,f149])).

fof(f170,plain,
    ( r1_tarski(u1_struct_0(sK1),sK2(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f162,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f481,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),sK2(sK0,u1_struct_0(sK1)))
    | m1_pre_topc(sK1,sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) ),
    inference(superposition,[],[f153,f262])).

fof(f262,plain,(
    sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f261,f31])).

fof(f261,plain,
    ( sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f260,f32])).

fof(f260,plain,
    ( sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f259,f34])).

fof(f259,plain,
    ( sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f258,f237])).

fof(f258,plain,
    ( sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f236,f176])).

fof(f236,plain,
    ( sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK3(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f186,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK3(X0,X1)) = X1
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f153,plain,(
    ! [X1] :
      ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X1))
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f152,f32])).

fof(f152,plain,(
    ! [X1] :
      ( m1_pre_topc(sK1,X1)
      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f34])).

fof(f143,plain,(
    ! [X1] :
      ( m1_pre_topc(sK1,X1)
      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

%------------------------------------------------------------------------------
