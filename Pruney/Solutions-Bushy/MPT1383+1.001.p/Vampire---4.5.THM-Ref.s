%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1383+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:51 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 351 expanded)
%              Number of leaves         :    7 (  69 expanded)
%              Depth                    :   20
%              Number of atoms          :  374 (2390 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f89,f117])).

fof(f117,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f115,f34])).

fof(f34,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl5_1
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f115,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f114,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f114,plain,
    ( v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f113,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f113,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f112,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f112,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f111,f23])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f111,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f106,f22])).

fof(f22,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f106,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f105,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f105,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f101,f90])).

fof(f90,plain,
    ( r2_hidden(sK1,sK3)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f18,f34])).

fof(f18,plain,
    ( r2_hidden(sK1,sK3)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f101,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3)
        | r2_hidden(X1,k1_tops_1(sK0,sK2)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f100,f44])).

fof(f44,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl5_3
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f100,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK3,sK2)
        | ~ r2_hidden(X1,sK3)
        | r2_hidden(X1,k1_tops_1(sK0,sK2)) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f99,f39])).

fof(f39,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl5_2
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f99,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(sK3,sK0)
        | ~ r1_tarski(sK3,sK2)
        | ~ r2_hidden(X1,sK3)
        | r2_hidden(X1,k1_tops_1(sK0,sK2)) )
    | spl5_1 ),
    inference(resolution,[],[f95,f91])).

fof(f91,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f15,f34])).

fof(f15,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,sK2)
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X1,k1_tops_1(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f94,f22])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,sK2)
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X1,k1_tops_1(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f92,f23])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,sK2)
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X1,k1_tops_1(sK0,sK2)) ) ),
    inference(resolution,[],[f30,f19])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(f89,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f87,f78])).

fof(f78,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f77,f22])).

fof(f77,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f76,f19])).

fof(f76,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f70,f23])).

fof(f70,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f67,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,sK4(X0,X1,X2))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f66,f21])).

fof(f66,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f65,f20])).

fof(f65,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f64,f23])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f63,f22])).

fof(f63,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f62,f35])).

fof(f35,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f87,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f86,f81])).

fof(f81,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f80,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f79,f19])).

fof(f79,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f71,f23])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f67,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK4(X0,X1,X2),X2)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f86,plain,
    ( ~ r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f85,f84])).

fof(f84,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f83,f22])).

fof(f83,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f82,f19])).

fof(f82,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f72,f23])).

fof(f72,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f67,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f85,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f75,f46])).

fof(f46,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2)
        | ~ r2_hidden(sK1,X3) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f14,f35])).

fof(f14,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_connsp_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f74,f22])).

fof(f74,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f73,f19])).

fof(f73,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f69,f23])).

fof(f69,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f67,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f17,f42,f33])).

fof(f17,plain,
    ( r1_tarski(sK3,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f16,f37,f33])).

fof(f16,plain,
    ( v3_pre_topc(sK3,sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
