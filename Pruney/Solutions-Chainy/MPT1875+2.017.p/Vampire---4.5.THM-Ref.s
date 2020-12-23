%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:33 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 114 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  294 ( 547 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f137,f193])).

fof(f193,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f191,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f191,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f189,f32])).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f189,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(resolution,[],[f184,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f184,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f180,f30])).

fof(f180,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(resolution,[],[f146,f31])).

fof(f31,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f146,plain,
    ( ! [X3] :
        ( v2_tex_2(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_3 ),
    inference(resolution,[],[f136,f46])).

fof(f46,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f136,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X2,sK0) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_3
  <=> ! [X2] :
        ( v2_tex_2(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f137,plain,
    ( spl4_2
    | spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f104,f80,f135,f80])).

fof(f80,plain,
    ( spl4_2
  <=> ! [X1,X0] :
        ( ~ sQ3_eqProxy(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,X1)
        | ~ sQ3_eqProxy(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f104,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sQ3_eqProxy(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ sQ3_eqProxy(X1,u1_struct_0(sK0))
      | v2_tex_2(X2,sK0)
      | ~ r1_tarski(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,X0)
      | ~ sQ3_eqProxy(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,X3)
      | ~ sQ3_eqProxy(X4,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f103,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sQ3_eqProxy(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ sQ3_eqProxy(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v2_tex_2(X2,sK0)
      | ~ r1_tarski(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,X0)
      | ~ sQ3_eqProxy(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,X3)
      | ~ sQ3_eqProxy(X4,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f101,f28])).

fof(f28,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_tdlat_3(sK0)
      | ~ sQ3_eqProxy(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ sQ3_eqProxy(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v2_tex_2(X2,sK0)
      | ~ r1_tarski(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,X0)
      | ~ sQ3_eqProxy(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,X3)
      | ~ sQ3_eqProxy(X4,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f83,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v1_tdlat_3(X1)
      | ~ sQ3_eqProxy(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sQ3_eqProxy(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | v2_tex_2(X3,X1)
      | ~ r1_tarski(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,X2)
      | ~ sQ3_eqProxy(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,X4)
      | ~ sQ3_eqProxy(X5,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f71,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X1,X3)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ m1_subset_1(X0,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sQ3_eqProxy(X0,u1_struct_0(X2))
      | ~ v1_tdlat_3(X2)
      | ~ sQ3_eqProxy(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | v2_tex_2(X3,X2)
      | ~ r1_tarski(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ sQ3_eqProxy(X0,u1_struct_0(X2))
      | ~ v1_tdlat_3(X2)
      | ~ sQ3_eqProxy(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | v2_tex_2(X3,X2)
      | ~ r1_tarski(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f68,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | v2_tex_2(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

fof(f68,plain,(
    ! [X4,X5,X3] :
      ( v2_tex_2(u1_struct_0(X4),X4)
      | ~ m1_subset_1(X5,X3)
      | ~ sQ3_eqProxy(X5,u1_struct_0(X4))
      | ~ v1_tdlat_3(X4)
      | ~ sQ3_eqProxy(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f57,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | v2_tex_2(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_tdlat_3(X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_tdlat_3(X0) )
            & ( v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) ) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

fof(f88,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f48,f34,f64,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | ~ sQ3_eqProxy(X0,u1_struct_0(sK0))
        | ~ sQ3_eqProxy(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f64,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f47])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f48,plain,(
    ! [X0] : sQ3_eqProxy(k2_subset_1(X0),X0) ),
    inference(equality_proxy_replacement,[],[f33,f47])).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:40:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.48  % (28698)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.48  % (28693)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.23/0.48  % (28700)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.23/0.49  % (28698)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % (28706)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f194,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(avatar_sat_refutation,[],[f88,f137,f193])).
% 0.23/0.50  fof(f193,plain,(
% 0.23/0.50    ~spl4_3),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f192])).
% 0.23/0.50  fof(f192,plain,(
% 0.23/0.50    $false | ~spl4_3),
% 0.23/0.50    inference(subsumption_resolution,[],[f191,f30])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.50    inference(cnf_transformation,[],[f21])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & ~v2_struct_0(sK0)),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20,f19])).
% 0.23/0.50  fof(f19,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & ~v2_struct_0(sK0))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f20,plain,(
% 0.23/0.50    ? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f12,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0))),
% 0.23/0.50    inference(flattening,[],[f11])).
% 0.23/0.50  fof(f11,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f10])).
% 0.23/0.50  fof(f10,plain,(
% 0.23/0.50    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.23/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.23/0.50  fof(f9,negated_conjecture,(
% 0.23/0.50    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.23/0.50    inference(negated_conjecture,[],[f8])).
% 0.23/0.50  fof(f8,conjecture,(
% 0.23/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.23/0.50  fof(f191,plain,(
% 0.23/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 0.23/0.50    inference(subsumption_resolution,[],[f189,f32])).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.23/0.50  fof(f189,plain,(
% 0.23/0.50    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 0.23/0.50    inference(resolution,[],[f184,f38])).
% 0.23/0.50  fof(f38,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f18])).
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.23/0.50    inference(flattening,[],[f17])).
% 0.23/0.50  fof(f17,plain,(
% 0.23/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.23/0.50    inference(ennf_transformation,[],[f5])).
% 0.23/0.50  fof(f5,axiom,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.23/0.50  fof(f184,plain,(
% 0.23/0.50    ~r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 0.23/0.50    inference(subsumption_resolution,[],[f180,f30])).
% 0.23/0.50  fof(f180,plain,(
% 0.23/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 0.23/0.50    inference(resolution,[],[f146,f31])).
% 0.23/0.50  fof(f31,plain,(
% 0.23/0.50    ~v2_tex_2(sK1,sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f21])).
% 0.23/0.50  fof(f146,plain,(
% 0.23/0.50    ( ! [X3] : (v2_tex_2(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_3),
% 0.23/0.50    inference(resolution,[],[f136,f46])).
% 0.23/0.50  fof(f46,plain,(
% 0.23/0.50    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(equality_resolution,[],[f39])).
% 0.23/0.50  fof(f39,plain,(
% 0.23/0.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.23/0.50    inference(cnf_transformation,[],[f26])).
% 0.23/0.50  fof(f26,plain,(
% 0.23/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 0.23/0.50  fof(f25,plain,(
% 0.23/0.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.50    inference(rectify,[],[f23])).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.50    inference(nnf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.23/0.50  fof(f136,plain,(
% 0.23/0.50    ( ! [X2] : (~r1_tarski(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X2,sK0)) ) | ~spl4_3),
% 0.23/0.50    inference(avatar_component_clause,[],[f135])).
% 0.23/0.50  fof(f135,plain,(
% 0.23/0.50    spl4_3 <=> ! [X2] : (v2_tex_2(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,u1_struct_0(sK0)))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.50  fof(f137,plain,(
% 0.23/0.50    spl4_2 | spl4_3 | spl4_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f104,f80,f135,f80])).
% 0.23/0.50  fof(f80,plain,(
% 0.23/0.50    spl4_2 <=> ! [X1,X0] : (~sQ3_eqProxy(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,X1) | ~sQ3_eqProxy(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.50  fof(f104,plain,(
% 0.23/0.50    ( ! [X4,X2,X0,X3,X1] : (~sQ3_eqProxy(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ3_eqProxy(X1,u1_struct_0(sK0)) | v2_tex_2(X2,sK0) | ~r1_tarski(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,X0) | ~sQ3_eqProxy(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,X3) | ~sQ3_eqProxy(X4,u1_struct_0(sK0))) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f103,f27])).
% 0.23/0.50  fof(f27,plain,(
% 0.23/0.50    ~v2_struct_0(sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f21])).
% 0.23/0.50  fof(f103,plain,(
% 0.23/0.50    ( ! [X4,X2,X0,X3,X1] : (~sQ3_eqProxy(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ3_eqProxy(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_tex_2(X2,sK0) | ~r1_tarski(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,X0) | ~sQ3_eqProxy(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,X3) | ~sQ3_eqProxy(X4,u1_struct_0(sK0))) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f101,f28])).
% 0.23/0.50  fof(f28,plain,(
% 0.23/0.50    v1_tdlat_3(sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f21])).
% 0.23/0.50  fof(f101,plain,(
% 0.23/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_tdlat_3(sK0) | ~sQ3_eqProxy(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ3_eqProxy(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_tex_2(X2,sK0) | ~r1_tarski(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,X0) | ~sQ3_eqProxy(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,X3) | ~sQ3_eqProxy(X4,u1_struct_0(sK0))) )),
% 0.23/0.50    inference(resolution,[],[f83,f29])).
% 0.23/0.50  fof(f29,plain,(
% 0.23/0.50    l1_pre_topc(sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f21])).
% 0.23/0.50  fof(f83,plain,(
% 0.23/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~l1_pre_topc(X1) | ~v1_tdlat_3(X1) | ~sQ3_eqProxy(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~sQ3_eqProxy(X0,u1_struct_0(X1)) | v2_struct_0(X1) | v2_tex_2(X3,X1) | ~r1_tarski(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,X2) | ~sQ3_eqProxy(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,X4) | ~sQ3_eqProxy(X5,u1_struct_0(X1))) )),
% 0.23/0.50    inference(resolution,[],[f71,f57])).
% 0.23/0.50  fof(f57,plain,(
% 0.23/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X1,X3) | ~sQ3_eqProxy(X2,X3) | ~m1_subset_1(X0,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.23/0.50    inference(equality_proxy_axiom,[],[f47])).
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.23/0.50    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.23/0.50  fof(f71,plain,(
% 0.23/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sQ3_eqProxy(X0,u1_struct_0(X2)) | ~v1_tdlat_3(X2) | ~sQ3_eqProxy(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | v2_struct_0(X2) | v2_tex_2(X3,X2) | ~r1_tarski(X3,u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X0,X1)) )),
% 0.23/0.50    inference(duplicate_literal_removal,[],[f69])).
% 0.23/0.50  fof(f69,plain,(
% 0.23/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,X1) | ~sQ3_eqProxy(X0,u1_struct_0(X2)) | ~v1_tdlat_3(X2) | ~sQ3_eqProxy(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | v2_struct_0(X2) | v2_tex_2(X3,X2) | ~r1_tarski(X3,u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.23/0.50    inference(resolution,[],[f68,f35])).
% 0.23/0.50  fof(f35,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~v2_tex_2(X1,X0) | v2_tex_2(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f14])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(flattening,[],[f13])).
% 0.23/0.50  fof(f13,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f7])).
% 0.23/0.50  fof(f7,axiom,(
% 0.23/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).
% 0.23/0.50  fof(f68,plain,(
% 0.23/0.50    ( ! [X4,X5,X3] : (v2_tex_2(u1_struct_0(X4),X4) | ~m1_subset_1(X5,X3) | ~sQ3_eqProxy(X5,u1_struct_0(X4)) | ~v1_tdlat_3(X4) | ~sQ3_eqProxy(X3,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.23/0.50    inference(resolution,[],[f57,f43])).
% 0.23/0.50  fof(f43,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | v2_tex_2(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(equality_resolution,[],[f37])).
% 0.23/0.50  fof(f37,plain,(
% 0.23/0.50    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_tdlat_3(X0) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f22])).
% 0.23/0.50  fof(f22,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_tdlat_3(X0)) & (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0))) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.50    inference(nnf_transformation,[],[f16])).
% 0.23/0.50  fof(f16,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.50    inference(flattening,[],[f15])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f6])).
% 0.23/0.50  fof(f6,axiom,(
% 0.23/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).
% 0.23/0.50  fof(f88,plain,(
% 0.23/0.50    ~spl4_2),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f84])).
% 0.23/0.50  fof(f84,plain,(
% 0.23/0.50    $false | ~spl4_2),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f48,f34,f64,f81])).
% 0.23/0.50  fof(f81,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | ~sQ3_eqProxy(X0,u1_struct_0(sK0)) | ~sQ3_eqProxy(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_2),
% 0.23/0.50    inference(avatar_component_clause,[],[f80])).
% 0.23/0.50  fof(f64,plain,(
% 0.23/0.50    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.23/0.50    inference(equality_proxy_axiom,[],[f47])).
% 0.23/0.50  fof(f34,plain,(
% 0.23/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f3])).
% 0.23/0.50  fof(f3,axiom,(
% 0.23/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.23/0.50  fof(f48,plain,(
% 0.23/0.50    ( ! [X0] : (sQ3_eqProxy(k2_subset_1(X0),X0)) )),
% 0.23/0.50    inference(equality_proxy_replacement,[],[f33,f47])).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.23/0.50    inference(cnf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (28698)------------------------------
% 0.23/0.50  % (28698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (28698)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (28698)Memory used [KB]: 6268
% 0.23/0.50  % (28693)Refutation not found, incomplete strategy% (28693)------------------------------
% 0.23/0.50  % (28693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (28693)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (28693)Memory used [KB]: 6140
% 0.23/0.50  % (28693)Time elapsed: 0.060 s
% 0.23/0.50  % (28693)------------------------------
% 0.23/0.50  % (28693)------------------------------
% 0.23/0.50  % (28698)Time elapsed: 0.062 s
% 0.23/0.50  % (28698)------------------------------
% 0.23/0.50  % (28698)------------------------------
% 0.23/0.50  % (28691)Success in time 0.128 s
%------------------------------------------------------------------------------
