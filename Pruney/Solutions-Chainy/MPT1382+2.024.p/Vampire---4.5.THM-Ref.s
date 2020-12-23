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
% DateTime   : Thu Dec  3 13:15:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 310 expanded)
%              Number of leaves         :   14 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  324 (2082 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f196,f277,f280])).

fof(f280,plain,
    ( spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f278,f131])).

fof(f131,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl4_8
  <=> v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f278,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | spl4_6 ),
    inference(subsumption_resolution,[],[f267,f85])).

fof(f85,plain,
    ( ~ sP3(k1_tops_1(sK0,sK2))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_6
  <=> sP3(k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f267,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | sP3(k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f238,f46])).

fof(f46,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP3(X1) ) ),
    inference(cnf_transformation,[],[f46_D])).

fof(f46_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP3(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f238,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    inference(resolution,[],[f236,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f236,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f234,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f234,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f107,f76])).

fof(f76,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f75,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f35,f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f107,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_tops_1(sK0,sK2),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f106,f80])).

fof(f80,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f79,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f106,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
      | ~ r1_tarski(k1_tops_1(sK0,sK2),X1)
      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f104,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
      | ~ r1_tarski(k1_tops_1(sK0,sK2),X1)
      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f36,f89])).

fof(f89,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f88,f34])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f41,f29])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
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
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f277,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f275,f127])).

fof(f127,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_7
  <=> m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f275,plain,(
    m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) ),
    inference(resolution,[],[f249,f192])).

fof(f192,plain,(
    r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f191,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f191,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f178,f30])).

fof(f30,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f178,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(sK2,sK0,X0)
      | r2_hidden(X0,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f177,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f177,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X0,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f176,f34])).

fof(f176,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X0,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f171,f33])).

fof(f171,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X0,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f38,f29])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f249,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_tops_1(sK0,sK2))
      | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X1) ) ),
    inference(subsumption_resolution,[],[f248,f80])).

fof(f248,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
      | ~ r2_hidden(X1,k1_tops_1(sK0,sK2))
      | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X1) ) ),
    inference(subsumption_resolution,[],[f247,f32])).

fof(f247,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
      | ~ r2_hidden(X1,k1_tops_1(sK0,sK2))
      | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X1) ) ),
    inference(subsumption_resolution,[],[f246,f34])).

fof(f246,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
      | ~ r2_hidden(X1,k1_tops_1(sK0,sK2))
      | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X1) ) ),
    inference(subsumption_resolution,[],[f241,f33])).

fof(f241,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
      | ~ r2_hidden(X1,k1_tops_1(sK0,sK2))
      | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X1) ) ),
    inference(resolution,[],[f210,f89])).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f39,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
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
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f196,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f195,f84])).

fof(f195,plain,(
    ~ sP3(k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f192,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP3(X1) ) ),
    inference(general_splitting,[],[f45,f46_D])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f132,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f97,f129,f125])).

fof(f97,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) ),
    inference(subsumption_resolution,[],[f96,f76])).

fof(f96,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f90,f80])).

fof(f90,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f89,f28])).

fof(f28,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK2) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (9877)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.44  % (9877)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % (9885)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f281,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f132,f196,f277,f280])).
% 0.20/0.44  fof(f280,plain,(
% 0.20/0.44    spl4_6 | ~spl4_8),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f279])).
% 0.20/0.44  fof(f279,plain,(
% 0.20/0.44    $false | (spl4_6 | ~spl4_8)),
% 0.20/0.44    inference(subsumption_resolution,[],[f278,f131])).
% 0.20/0.44  fof(f131,plain,(
% 0.20/0.44    v1_xboole_0(k1_tops_1(sK0,sK2)) | ~spl4_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f129])).
% 0.20/0.44  fof(f129,plain,(
% 0.20/0.44    spl4_8 <=> v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.44  fof(f278,plain,(
% 0.20/0.44    ~v1_xboole_0(k1_tops_1(sK0,sK2)) | spl4_6),
% 0.20/0.44    inference(subsumption_resolution,[],[f267,f85])).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    ~sP3(k1_tops_1(sK0,sK2)) | spl4_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f84])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    spl4_6 <=> sP3(k1_tops_1(sK0,sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.44  fof(f267,plain,(
% 0.20/0.44    ~v1_xboole_0(k1_tops_1(sK0,sK2)) | sP3(k1_tops_1(sK0,sK2))),
% 0.20/0.44    inference(resolution,[],[f238,f46])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP3(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f46_D])).
% 0.20/0.44  fof(f46_D,plain,(
% 0.20/0.44    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP3(X1)) )),
% 0.20/0.44    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.44  fof(f238,plain,(
% 0.20/0.44    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,sK2)))),
% 0.20/0.44    inference(resolution,[],[f236,f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.44  fof(f236,plain,(
% 0.20/0.44    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))),
% 0.20/0.44    inference(subsumption_resolution,[],[f234,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,negated_conjecture,(
% 0.20/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.44    inference(negated_conjecture,[],[f10])).
% 0.20/0.44  fof(f10,conjecture,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.20/0.44  fof(f234,plain,(
% 0.20/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))),
% 0.20/0.44    inference(resolution,[],[f107,f76])).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.20/0.44    inference(subsumption_resolution,[],[f75,f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    l1_pre_topc(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.20/0.44    inference(resolution,[],[f35,f29])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.44  fof(f107,plain,(
% 0.20/0.44    ( ! [X1] : (~r1_tarski(k1_tops_1(sK0,sK2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X1))) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f106,f80])).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f79,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    v2_pre_topc(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f79,plain,(
% 0.20/0.44    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f78,f34])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.20/0.44    inference(resolution,[],[f40,f29])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(flattening,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.45  fof(f106,plain,(
% 0.20/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r1_tarski(k1_tops_1(sK0,sK2),X1) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X1))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f104,f34])).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r1_tarski(k1_tops_1(sK0,sK2),X1) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X1))) )),
% 0.20/0.45    inference(resolution,[],[f36,f89])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(subsumption_resolution,[],[f88,f34])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(resolution,[],[f41,f29])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.20/0.45  fof(f277,plain,(
% 0.20/0.45    spl4_7),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f276])).
% 0.20/0.45  fof(f276,plain,(
% 0.20/0.45    $false | spl4_7),
% 0.20/0.45    inference(subsumption_resolution,[],[f275,f127])).
% 0.20/0.45  fof(f127,plain,(
% 0.20/0.45    ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | spl4_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f125])).
% 0.20/0.45  fof(f125,plain,(
% 0.20/0.45    spl4_7 <=> m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.45  fof(f275,plain,(
% 0.20/0.45    m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)),
% 0.20/0.45    inference(resolution,[],[f249,f192])).
% 0.20/0.45  fof(f192,plain,(
% 0.20/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.20/0.45    inference(subsumption_resolution,[],[f191,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f191,plain,(
% 0.20/0.45    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.45    inference(resolution,[],[f178,f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f178,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_connsp_2(sK2,sK0,X0) | r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f177,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f177,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f176,f34])).
% 0.20/0.45  fof(f176,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f171,f33])).
% 0.20/0.45  fof(f171,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X0)) )),
% 0.20/0.45    inference(resolution,[],[f38,f29])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.20/0.45  fof(f249,plain,(
% 0.20/0.45    ( ! [X1] : (~r2_hidden(X1,k1_tops_1(sK0,sK2)) | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X1)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f248,f80])).
% 0.20/0.45  fof(f248,plain,(
% 0.20/0.45    ( ! [X1] : (~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r2_hidden(X1,k1_tops_1(sK0,sK2)) | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X1)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f247,f32])).
% 0.20/0.45  fof(f247,plain,(
% 0.20/0.45    ( ! [X1] : (v2_struct_0(sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r2_hidden(X1,k1_tops_1(sK0,sK2)) | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X1)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f246,f34])).
% 0.20/0.45  fof(f246,plain,(
% 0.20/0.45    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r2_hidden(X1,k1_tops_1(sK0,sK2)) | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X1)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f241,f33])).
% 0.20/0.45  fof(f241,plain,(
% 0.20/0.45    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r2_hidden(X1,k1_tops_1(sK0,sK2)) | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X1)) )),
% 0.20/0.45    inference(resolution,[],[f210,f89])).
% 0.20/0.45  fof(f210,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f39,f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.20/0.45  fof(f196,plain,(
% 0.20/0.45    ~spl4_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f195,f84])).
% 0.20/0.45  fof(f195,plain,(
% 0.20/0.45    ~sP3(k1_tops_1(sK0,sK2))),
% 0.20/0.45    inference(resolution,[],[f192,f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP3(X1)) )),
% 0.20/0.45    inference(general_splitting,[],[f45,f46_D])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.45  fof(f132,plain,(
% 0.20/0.45    ~spl4_7 | spl4_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f97,f129,f125])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    v1_xboole_0(k1_tops_1(sK0,sK2)) | ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f96,f76])).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    v1_xboole_0(k1_tops_1(sK0,sK2)) | ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f90,f80])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    v1_xboole_0(k1_tops_1(sK0,sK2)) | ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.20/0.45    inference(resolution,[],[f89,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3) | ~m1_connsp_2(X3,sK0,sK1) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (9877)------------------------------
% 0.20/0.45  % (9877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (9877)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (9877)Memory used [KB]: 5373
% 0.20/0.45  % (9877)Time elapsed: 0.048 s
% 0.20/0.45  % (9877)------------------------------
% 0.20/0.45  % (9877)------------------------------
% 0.20/0.45  % (9869)Success in time 0.095 s
%------------------------------------------------------------------------------
