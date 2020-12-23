%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 319 expanded)
%              Number of leaves         :   12 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  462 (2051 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f237,f291])).

fof(f291,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f289,f54])).

fof(f54,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_1
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f289,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f287,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f287,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f279,f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f139,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f138,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f138,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f136,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f37,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f279,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f277,f258])).

fof(f258,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | r2_hidden(sK1,X0) )
    | spl6_1 ),
    inference(resolution,[],[f257,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f257,plain,
    ( r2_hidden(sK1,sK3)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f30,f54])).

fof(f30,plain,
    ( r2_hidden(sK1,sK3)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f277,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f274,f64])).

fof(f64,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_3
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f274,plain,
    ( ~ r1_tarski(sK3,sK2)
    | r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f256,f31])).

fof(f256,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3,X1)
        | r1_tarski(sK3,k1_tops_1(sK0,X1)) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f255,f59])).

fof(f59,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_2
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f255,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK3,sK0)
        | ~ r1_tarski(sK3,X1)
        | r1_tarski(sK3,k1_tops_1(sK0,X1)) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f249,f35])).

fof(f249,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK3,sK0)
        | ~ r1_tarski(sK3,X1)
        | r1_tarski(sK3,k1_tops_1(sK0,X1)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f246,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f246,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3 ),
    inference(resolution,[],[f242,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f242,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f239,f81])).

fof(f81,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f50,f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f239,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | r1_tarski(sK3,X1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f64,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f237,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f235,f180])).

fof(f180,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f179,f164])).

fof(f164,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f163,f33])).

fof(f163,plain,
    ( v2_struct_0(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f162,f32])).

fof(f162,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f161,f35])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f160,f34])).

fof(f160,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f159,f55])).

fof(f55,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r1_tarski(sK4(X0,X1,X2),X2) ) ),
    inference(subsumption_resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r1_tarski(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f179,plain,
    ( ~ r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f174,f158])).

fof(f158,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f157,f33])).

fof(f157,plain,
    ( v2_struct_0(sK0)
    | v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f156,f32])).

fof(f156,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f155,f35])).

fof(f155,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f154,f34])).

fof(f154,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f153,f55])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v3_pre_topc(sK4(X0,X1,X2),X0) ) ),
    inference(subsumption_resolution,[],[f42,f45])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | v3_pre_topc(sK4(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f174,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f173,f66])).

fof(f66,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2)
        | ~ r2_hidden(sK1,X3) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f26,f55])).

fof(f26,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_connsp_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f173,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_1 ),
    inference(resolution,[],[f169,f49])).

fof(f169,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl6_1 ),
    inference(resolution,[],[f166,f81])).

fof(f166,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | r1_tarski(sK4(sK0,sK1,sK2),X1) )
    | ~ spl6_1 ),
    inference(resolution,[],[f164,f51])).

fof(f235,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f234,f33])).

fof(f234,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f233,f32])).

fof(f233,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f232,f35])).

fof(f232,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f214,f34])).

fof(f214,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f209,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X1,X0,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f44,f45])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f209,plain,
    ( m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f208,f33])).

fof(f208,plain,
    ( v2_struct_0(sK0)
    | m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f207,f32])).

fof(f207,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f206,f35])).

fof(f206,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f205,f34])).

fof(f205,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ spl6_1 ),
    inference(resolution,[],[f187,f55])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_connsp_2(sK4(X0,X1,X2),X0,X1) ) ),
    inference(subsumption_resolution,[],[f41,f45])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_connsp_2(sK4(X0,X1,X2),X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f29,f62,f53])).

fof(f29,plain,
    ( r1_tarski(sK3,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f28,f57,f53])).

fof(f28,plain,
    ( v3_pre_topc(sK3,sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:28:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (24032)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.47  % (24045)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.47  % (24037)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.47  % (24032)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (24040)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.47  % (24040)Refutation not found, incomplete strategy% (24040)------------------------------
% 0.22/0.47  % (24040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (24040)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (24040)Memory used [KB]: 5373
% 0.22/0.47  % (24040)Time elapsed: 0.058 s
% 0.22/0.47  % (24040)------------------------------
% 0.22/0.47  % (24040)------------------------------
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f292,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f60,f65,f237,f291])).
% 0.22/0.47  fof(f291,plain,(
% 0.22/0.47    spl6_1 | ~spl6_2 | ~spl6_3),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f290])).
% 0.22/0.47  fof(f290,plain,(
% 0.22/0.47    $false | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.47    inference(subsumption_resolution,[],[f289,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ~m1_connsp_2(sK2,sK0,sK1) | spl6_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    spl6_1 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.47  fof(f289,plain,(
% 0.22/0.47    m1_connsp_2(sK2,sK0,sK1) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.47    inference(subsumption_resolution,[],[f287,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f9])).
% 0.22/0.47  fof(f9,conjecture,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.22/0.47  fof(f287,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,sK1) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.47    inference(resolution,[],[f279,f140])).
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f139,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ~v2_struct_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f139,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f138,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    l1_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f138,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f136,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    v2_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f136,plain,(
% 0.22/0.47    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X0)) )),
% 0.22/0.47    inference(resolution,[],[f37,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.22/0.47  fof(f279,plain,(
% 0.22/0.47    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.47    inference(resolution,[],[f277,f258])).
% 0.22/0.47  fof(f258,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_tarski(sK3,X0) | r2_hidden(sK1,X0)) ) | spl6_1),
% 0.22/0.47    inference(resolution,[],[f257,f46])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.47  fof(f257,plain,(
% 0.22/0.47    r2_hidden(sK1,sK3) | spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f30,f54])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    r2_hidden(sK1,sK3) | m1_connsp_2(sK2,sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f277,plain,(
% 0.22/0.47    r1_tarski(sK3,k1_tops_1(sK0,sK2)) | (~spl6_2 | ~spl6_3)),
% 0.22/0.47    inference(subsumption_resolution,[],[f274,f64])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    r1_tarski(sK3,sK2) | ~spl6_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f62])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl6_3 <=> r1_tarski(sK3,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.47  fof(f274,plain,(
% 0.22/0.47    ~r1_tarski(sK3,sK2) | r1_tarski(sK3,k1_tops_1(sK0,sK2)) | (~spl6_2 | ~spl6_3)),
% 0.22/0.47    inference(resolution,[],[f256,f31])).
% 0.22/0.47  fof(f256,plain,(
% 0.22/0.47    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3,X1) | r1_tarski(sK3,k1_tops_1(sK0,X1))) ) | (~spl6_2 | ~spl6_3)),
% 0.22/0.47    inference(subsumption_resolution,[],[f255,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    v3_pre_topc(sK3,sK0) | ~spl6_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl6_2 <=> v3_pre_topc(sK3,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.47  fof(f255,plain,(
% 0.22/0.47    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~r1_tarski(sK3,X1) | r1_tarski(sK3,k1_tops_1(sK0,X1))) ) | ~spl6_3),
% 0.22/0.47    inference(subsumption_resolution,[],[f249,f35])).
% 0.22/0.47  fof(f249,plain,(
% 0.22/0.47    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~r1_tarski(sK3,X1) | r1_tarski(sK3,k1_tops_1(sK0,X1))) ) | ~spl6_3),
% 0.22/0.47    inference(resolution,[],[f246,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.22/0.47  fof(f246,plain,(
% 0.22/0.47    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_3),
% 0.22/0.47    inference(resolution,[],[f242,f49])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.47  fof(f242,plain,(
% 0.22/0.47    r1_tarski(sK3,u1_struct_0(sK0)) | ~spl6_3),
% 0.22/0.47    inference(resolution,[],[f239,f81])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.22/0.47    inference(resolution,[],[f50,f31])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f239,plain,(
% 0.22/0.47    ( ! [X1] : (~r1_tarski(sK2,X1) | r1_tarski(sK3,X1)) ) | ~spl6_3),
% 0.22/0.47    inference(resolution,[],[f64,f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.47  fof(f237,plain,(
% 0.22/0.47    ~spl6_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f236])).
% 0.22/0.47  fof(f236,plain,(
% 0.22/0.47    $false | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f235,f180])).
% 0.22/0.47  fof(f180,plain,(
% 0.22/0.47    ~r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f179,f164])).
% 0.22/0.47  fof(f164,plain,(
% 0.22/0.47    r1_tarski(sK4(sK0,sK1,sK2),sK2) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f163,f33])).
% 0.22/0.47  fof(f163,plain,(
% 0.22/0.47    v2_struct_0(sK0) | r1_tarski(sK4(sK0,sK1,sK2),sK2) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f162,f32])).
% 0.22/0.47  fof(f162,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r1_tarski(sK4(sK0,sK1,sK2),sK2) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f161,f35])).
% 0.22/0.47  fof(f161,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r1_tarski(sK4(sK0,sK1,sK2),sK2) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f160,f34])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r1_tarski(sK4(sK0,sK1,sK2),sK2) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f159,f55])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    m1_connsp_2(sK2,sK0,sK1) | ~spl6_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f53])).
% 0.22/0.47  fof(f159,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r1_tarski(sK4(X0,X1,X2),X2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f43,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | r1_tarski(sK4(X0,X1,X2),X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.22/0.47  fof(f179,plain,(
% 0.22/0.47    ~r1_tarski(sK4(sK0,sK1,sK2),sK2) | ~r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f174,f158])).
% 0.22/0.47  fof(f158,plain,(
% 0.22/0.47    v3_pre_topc(sK4(sK0,sK1,sK2),sK0) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f157,f33])).
% 0.22/0.47  fof(f157,plain,(
% 0.22/0.47    v2_struct_0(sK0) | v3_pre_topc(sK4(sK0,sK1,sK2),sK0) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f156,f32])).
% 0.22/0.47  fof(f156,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK4(sK0,sK1,sK2),sK0) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f155,f35])).
% 0.22/0.47  fof(f155,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK4(sK0,sK1,sK2),sK0) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f154,f34])).
% 0.22/0.47  fof(f154,plain,(
% 0.22/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK4(sK0,sK1,sK2),sK0) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f153,f55])).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v3_pre_topc(sK4(X0,X1,X2),X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f42,f45])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | v3_pre_topc(sK4(X0,X1,X2),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f174,plain,(
% 0.22/0.47    ~v3_pre_topc(sK4(sK0,sK1,sK2),sK0) | ~r1_tarski(sK4(sK0,sK1,sK2),sK2) | ~r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f173,f66])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2) | ~r2_hidden(sK1,X3)) ) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f26,f55])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2) | ~r2_hidden(sK1,X3) | ~m1_connsp_2(sK2,sK0,sK1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f173,plain,(
% 0.22/0.47    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f169,f49])).
% 0.22/0.47  fof(f169,plain,(
% 0.22/0.47    r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK0)) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f166,f81])).
% 0.22/0.47  fof(f166,plain,(
% 0.22/0.47    ( ! [X1] : (~r1_tarski(sK2,X1) | r1_tarski(sK4(sK0,sK1,sK2),X1)) ) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f164,f51])).
% 0.22/0.47  fof(f235,plain,(
% 0.22/0.47    r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f234,f33])).
% 0.22/0.47  fof(f234,plain,(
% 0.22/0.47    v2_struct_0(sK0) | r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f233,f32])).
% 0.22/0.47  fof(f233,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f232,f35])).
% 0.22/0.47  fof(f232,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f214,f34])).
% 0.22/0.47  fof(f214,plain,(
% 0.22/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f209,f112])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_connsp_2(X1,X0,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X2,X1)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f44,f45])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.22/0.47  fof(f209,plain,(
% 0.22/0.47    m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f208,f33])).
% 0.22/0.47  fof(f208,plain,(
% 0.22/0.47    v2_struct_0(sK0) | m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f207,f32])).
% 0.22/0.47  fof(f207,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f206,f35])).
% 0.22/0.47  fof(f206,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1) | ~spl6_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f205,f34])).
% 0.22/0.47  fof(f205,plain,(
% 0.22/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_connsp_2(sK4(sK0,sK1,sK2),sK0,sK1) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f187,f55])).
% 0.22/0.47  fof(f187,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_connsp_2(sK4(X0,X1,X2),X0,X1)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f41,f45])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | m1_connsp_2(sK4(X0,X1,X2),X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    spl6_1 | spl6_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f29,f62,f53])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    r1_tarski(sK3,sK2) | m1_connsp_2(sK2,sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    spl6_1 | spl6_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f28,f57,f53])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    v3_pre_topc(sK3,sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (24032)------------------------------
% 0.22/0.47  % (24032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (24032)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (24032)Memory used [KB]: 5373
% 0.22/0.47  % (24032)Time elapsed: 0.047 s
% 0.22/0.47  % (24032)------------------------------
% 0.22/0.47  % (24032)------------------------------
% 0.22/0.47  % (24031)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.47  % (24025)Success in time 0.109 s
%------------------------------------------------------------------------------
