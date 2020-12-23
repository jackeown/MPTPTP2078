%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:55 EST 2020

% Result     : Theorem 3.30s
% Output     : Refutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 190 expanded)
%              Number of leaves         :   10 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  206 (1080 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7868,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6588,f7867])).

fof(f7867,plain,(
    ~ spl5_27 ),
    inference(avatar_split_clause,[],[f7861,f6576])).

fof(f6576,plain,
    ( spl5_27
  <=> r1_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f7861,plain,(
    ~ r1_tarski(sK3,sK3) ),
    inference(resolution,[],[f7860,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f7860,plain,(
    ~ r1_tarski(sK3,k2_xboole_0(sK2,sK3)) ),
    inference(global_subsumption,[],[f1306,f7838])).

fof(f7838,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ r1_tarski(sK3,k2_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f6937,f1290])).

fof(f1290,plain,(
    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f30,f34,f1287])).

fof(f1287,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f103,f115])).

fof(f115,plain,(
    ! [X5] :
      ( k4_subset_1(u1_struct_0(sK0),sK2,X5) = k2_xboole_0(sK2,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f34,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f103,plain,(
    ! [X6] :
      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X6,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f30,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f6937,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ r1_tarski(sK3,X0) ) ),
    inference(superposition,[],[f147,f1750])).

fof(f1750,plain,(
    ! [X7] :
      ( k1_tops_1(sK0,X7) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X7))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK3,X7) ) ),
    inference(resolution,[],[f109,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f109,plain,(
    ! [X3] :
      ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X3))
      | ~ r1_tarski(sK3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f38,f100])).

fof(f100,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK3,X3)
      | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X3)) ) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f147,plain,(
    ! [X0] : r2_hidden(sK1,k2_xboole_0(k1_tops_1(sK0,sK3),X0)) ),
    inference(resolution,[],[f90,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f90,plain,(
    r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
    inference(global_subsumption,[],[f35,f36,f37,f38,f89,f88])).

fof(f88,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f32,plain,(
    m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f30])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f1306,plain,(
    ~ r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    inference(global_subsumption,[],[f154,f1290])).

fof(f154,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f36,f37,f38,f35,f149])).

fof(f149,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    inference(resolution,[],[f145,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f145,plain,(
    ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(global_subsumption,[],[f30,f34,f143])).

fof(f143,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f33,f52])).

fof(f33,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f6588,plain,(
    spl5_27 ),
    inference(avatar_contradiction_clause,[],[f6584])).

fof(f6584,plain,
    ( $false
    | spl5_27 ),
    inference(resolution,[],[f6578,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f6578,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f6576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (12380)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % (12389)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (12373)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (12370)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (12379)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (12390)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (12392)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (12383)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (12381)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (12388)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (12375)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (12377)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (12372)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (12378)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (12369)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (12394)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (12376)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (12382)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (12374)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (12385)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (12384)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (12391)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.54  % (12386)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (12393)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  % (12371)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.55  % (12387)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 2.22/0.65  % (12378)Refutation not found, incomplete strategy% (12378)------------------------------
% 2.22/0.65  % (12378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.65  % (12378)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.65  
% 2.22/0.65  % (12378)Memory used [KB]: 6140
% 2.22/0.65  % (12378)Time elapsed: 0.237 s
% 2.22/0.65  % (12378)------------------------------
% 2.22/0.65  % (12378)------------------------------
% 2.22/0.68  % (12386)Refutation not found, incomplete strategy% (12386)------------------------------
% 2.22/0.68  % (12386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (12386)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.68  
% 2.22/0.68  % (12386)Memory used [KB]: 6140
% 2.22/0.68  % (12386)Time elapsed: 0.271 s
% 2.22/0.68  % (12386)------------------------------
% 2.22/0.68  % (12386)------------------------------
% 3.30/0.83  % (12389)Refutation found. Thanks to Tanya!
% 3.30/0.83  % SZS status Theorem for theBenchmark
% 3.30/0.85  % SZS output start Proof for theBenchmark
% 3.30/0.85  fof(f7868,plain,(
% 3.30/0.85    $false),
% 3.30/0.85    inference(avatar_sat_refutation,[],[f6588,f7867])).
% 3.30/0.85  fof(f7867,plain,(
% 3.30/0.85    ~spl5_27),
% 3.30/0.85    inference(avatar_split_clause,[],[f7861,f6576])).
% 3.30/0.85  fof(f6576,plain,(
% 3.30/0.85    spl5_27 <=> r1_tarski(sK3,sK3)),
% 3.30/0.85    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 3.30/0.85  fof(f7861,plain,(
% 3.30/0.85    ~r1_tarski(sK3,sK3)),
% 3.30/0.85    inference(resolution,[],[f7860,f49])).
% 3.30/0.85  fof(f49,plain,(
% 3.30/0.85    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 3.30/0.85    inference(cnf_transformation,[],[f23])).
% 3.30/0.85  fof(f23,plain,(
% 3.30/0.85    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.30/0.85    inference(ennf_transformation,[],[f3])).
% 3.30/0.85  fof(f3,axiom,(
% 3.30/0.85    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.30/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.30/0.85  fof(f7860,plain,(
% 3.30/0.85    ~r1_tarski(sK3,k2_xboole_0(sK2,sK3))),
% 3.30/0.85    inference(global_subsumption,[],[f1306,f7838])).
% 3.30/0.85  fof(f7838,plain,(
% 3.30/0.85    r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~r1_tarski(sK3,k2_xboole_0(sK2,sK3))),
% 3.30/0.85    inference(resolution,[],[f6937,f1290])).
% 3.30/0.85  fof(f1290,plain,(
% 3.30/0.85    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.30/0.85    inference(global_subsumption,[],[f30,f34,f1287])).
% 3.30/0.85  fof(f1287,plain,(
% 3.30/0.85    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.30/0.85    inference(superposition,[],[f103,f115])).
% 3.30/0.86  fof(f115,plain,(
% 3.30/0.86    ( ! [X5] : (k4_subset_1(u1_struct_0(sK0),sK2,X5) = k2_xboole_0(sK2,X5) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 3.30/0.86    inference(resolution,[],[f34,f52])).
% 3.30/0.86  fof(f52,plain,(
% 3.30/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 3.30/0.86    inference(cnf_transformation,[],[f29])).
% 3.30/0.86  fof(f29,plain,(
% 3.30/0.86    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.30/0.86    inference(flattening,[],[f28])).
% 3.30/0.86  fof(f28,plain,(
% 3.30/0.86    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.30/0.86    inference(ennf_transformation,[],[f7])).
% 3.30/0.86  fof(f7,axiom,(
% 3.30/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.30/0.86  fof(f103,plain,(
% 3.30/0.86    ( ! [X6] : (m1_subset_1(k4_subset_1(u1_struct_0(sK0),X6,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 3.30/0.86    inference(resolution,[],[f30,f51])).
% 3.30/0.86  fof(f51,plain,(
% 3.30/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 3.30/0.86    inference(cnf_transformation,[],[f27])).
% 3.30/0.86  fof(f27,plain,(
% 3.30/0.86    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.30/0.86    inference(flattening,[],[f26])).
% 3.30/0.86  fof(f26,plain,(
% 3.30/0.86    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.30/0.86    inference(ennf_transformation,[],[f6])).
% 3.30/0.86  fof(f6,axiom,(
% 3.30/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.30/0.86  fof(f34,plain,(
% 3.30/0.86    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.30/0.86    inference(cnf_transformation,[],[f15])).
% 3.30/0.86  fof(f15,plain,(
% 3.30/0.86    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.30/0.86    inference(flattening,[],[f14])).
% 3.30/0.86  fof(f14,plain,(
% 3.30/0.86    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.30/0.86    inference(ennf_transformation,[],[f13])).
% 3.30/0.86  fof(f13,negated_conjecture,(
% 3.30/0.86    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 3.30/0.86    inference(negated_conjecture,[],[f12])).
% 3.30/0.86  fof(f12,conjecture,(
% 3.30/0.86    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).
% 3.30/0.86  fof(f30,plain,(
% 3.30/0.86    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.30/0.86    inference(cnf_transformation,[],[f15])).
% 3.30/0.86  fof(f6937,plain,(
% 3.30/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~r1_tarski(sK3,X0)) )),
% 3.30/0.86    inference(superposition,[],[f147,f1750])).
% 3.30/0.86  fof(f1750,plain,(
% 3.30/0.86    ( ! [X7] : (k1_tops_1(sK0,X7) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3,X7)) )),
% 3.30/0.86    inference(resolution,[],[f109,f42])).
% 3.30/0.86  fof(f42,plain,(
% 3.30/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.30/0.86    inference(cnf_transformation,[],[f20])).
% 3.30/0.86  fof(f20,plain,(
% 3.30/0.86    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.30/0.86    inference(ennf_transformation,[],[f4])).
% 3.30/0.86  fof(f4,axiom,(
% 3.30/0.86    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.30/0.86  fof(f109,plain,(
% 3.30/0.86    ( ! [X3] : (r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X3)) | ~r1_tarski(sK3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 3.30/0.86    inference(global_subsumption,[],[f38,f100])).
% 3.30/0.86  fof(f100,plain,(
% 3.30/0.86    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3,X3) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X3))) )),
% 3.30/0.86    inference(resolution,[],[f30,f39])).
% 3.30/0.86  fof(f39,plain,(
% 3.30/0.86    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 3.30/0.86    inference(cnf_transformation,[],[f17])).
% 3.30/0.86  fof(f17,plain,(
% 3.30/0.86    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.30/0.86    inference(flattening,[],[f16])).
% 3.30/0.86  fof(f16,plain,(
% 3.30/0.86    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.30/0.86    inference(ennf_transformation,[],[f9])).
% 3.30/0.86  fof(f9,axiom,(
% 3.30/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 3.30/0.86  fof(f38,plain,(
% 3.30/0.86    l1_pre_topc(sK0)),
% 3.30/0.86    inference(cnf_transformation,[],[f15])).
% 3.30/0.86  fof(f147,plain,(
% 3.30/0.86    ( ! [X0] : (r2_hidden(sK1,k2_xboole_0(k1_tops_1(sK0,sK3),X0))) )),
% 3.30/0.86    inference(resolution,[],[f90,f62])).
% 3.30/0.86  fof(f62,plain,(
% 3.30/0.86    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 3.30/0.86    inference(equality_resolution,[],[f57])).
% 3.30/0.86  fof(f57,plain,(
% 3.30/0.86    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.30/0.86    inference(cnf_transformation,[],[f1])).
% 3.30/0.86  fof(f1,axiom,(
% 3.30/0.86    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 3.30/0.86  fof(f90,plain,(
% 3.30/0.86    r2_hidden(sK1,k1_tops_1(sK0,sK3))),
% 3.30/0.86    inference(global_subsumption,[],[f35,f36,f37,f38,f89,f88])).
% 3.30/0.86  fof(f88,plain,(
% 3.30/0.86    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK3))),
% 3.30/0.86    inference(resolution,[],[f32,f41])).
% 3.30/0.86  fof(f41,plain,(
% 3.30/0.86    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 3.30/0.86    inference(cnf_transformation,[],[f19])).
% 3.30/0.86  fof(f19,plain,(
% 3.30/0.86    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.86    inference(flattening,[],[f18])).
% 3.30/0.86  fof(f18,plain,(
% 3.30/0.86    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/0.86    inference(ennf_transformation,[],[f10])).
% 3.30/0.86  fof(f10,axiom,(
% 3.30/0.86    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.30/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 3.30/0.86  fof(f32,plain,(
% 3.30/0.86    m1_connsp_2(sK3,sK0,sK1)),
% 3.30/0.86    inference(cnf_transformation,[],[f15])).
% 3.30/0.86  fof(f89,plain,(
% 3.30/0.86    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.30/0.86    inference(global_subsumption,[],[f30])).
% 3.30/0.86  fof(f37,plain,(
% 3.30/0.86    v2_pre_topc(sK0)),
% 3.30/0.86    inference(cnf_transformation,[],[f15])).
% 3.30/0.86  fof(f36,plain,(
% 3.30/0.86    ~v2_struct_0(sK0)),
% 3.30/0.86    inference(cnf_transformation,[],[f15])).
% 3.30/0.86  fof(f35,plain,(
% 3.30/0.86    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.30/0.86    inference(cnf_transformation,[],[f15])).
% 3.30/0.86  fof(f1306,plain,(
% 3.30/0.86    ~r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))),
% 3.30/0.86    inference(global_subsumption,[],[f154,f1290])).
% 3.30/0.86  fof(f154,plain,(
% 3.30/0.86    ~r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.30/0.86    inference(global_subsumption,[],[f36,f37,f38,f35,f149])).
% 3.30/0.86  fof(f149,plain,(
% 3.30/0.86    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))),
% 3.30/0.86    inference(resolution,[],[f145,f40])).
% 3.30/0.86  fof(f40,plain,(
% 3.30/0.86    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 3.30/0.86    inference(cnf_transformation,[],[f19])).
% 3.30/0.86  fof(f145,plain,(
% 3.30/0.86    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)),
% 3.30/0.86    inference(global_subsumption,[],[f30,f34,f143])).
% 3.30/0.86  fof(f143,plain,(
% 3.30/0.86    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.30/0.86    inference(superposition,[],[f33,f52])).
% 3.30/0.86  fof(f33,plain,(
% 3.30/0.86    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 3.30/0.86    inference(cnf_transformation,[],[f15])).
% 3.30/0.86  fof(f6588,plain,(
% 3.30/0.86    spl5_27),
% 3.30/0.86    inference(avatar_contradiction_clause,[],[f6584])).
% 3.30/0.86  fof(f6584,plain,(
% 3.30/0.86    $false | spl5_27),
% 3.30/0.86    inference(resolution,[],[f6578,f60])).
% 3.30/0.86  fof(f60,plain,(
% 3.30/0.86    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.30/0.86    inference(equality_resolution,[],[f44])).
% 3.30/0.86  fof(f44,plain,(
% 3.30/0.86    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.30/0.86    inference(cnf_transformation,[],[f2])).
% 3.99/0.86  fof(f2,axiom,(
% 3.99/0.86    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.99/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.99/0.86  fof(f6578,plain,(
% 3.99/0.86    ~r1_tarski(sK3,sK3) | spl5_27),
% 3.99/0.86    inference(avatar_component_clause,[],[f6576])).
% 3.99/0.86  % SZS output end Proof for theBenchmark
% 3.99/0.86  % (12389)------------------------------
% 3.99/0.86  % (12389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.99/0.86  % (12389)Termination reason: Refutation
% 3.99/0.86  
% 3.99/0.86  % (12389)Memory used [KB]: 19957
% 3.99/0.86  % (12389)Time elapsed: 0.421 s
% 3.99/0.86  % (12389)------------------------------
% 3.99/0.86  % (12389)------------------------------
% 3.99/0.86  % (12368)Success in time 0.507 s
%------------------------------------------------------------------------------
