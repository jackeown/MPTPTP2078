%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 362 expanded)
%              Number of leaves         :   22 ( 134 expanded)
%              Depth                    :   23
%              Number of atoms          :  571 (3292 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f686,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f202,f289,f335,f377,f676,f684])).

fof(f684,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f680])).

fof(f680,plain,
    ( $false
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f47,f49,f104])).

fof(f104,plain,
    ( ! [X3,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_1
  <=> ! [X1,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_connsp_2(X3,sK0,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X3) )
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f35,f34,f33])).

% (11402)Refutation not found, incomplete strategy% (11402)------------------------------
% (11402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11402)Termination reason: Refutation not found, incomplete strategy

% (11402)Memory used [KB]: 6140
% (11402)Time elapsed: 0.086 s
% (11402)------------------------------
% (11402)------------------------------
fof(f33,plain,
    ( ? [X0] :
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_connsp_2(X3,sK0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_connsp_2(X3,sK0,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                | v1_xboole_0(X3) )
            & m1_connsp_2(X2,sK0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_connsp_2(X3,sK0,sK1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
              | v1_xboole_0(X3) )
          & m1_connsp_2(X2,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X3,X2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_connsp_2(X3,sK0,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
            | v1_xboole_0(X3) )
        & m1_connsp_2(X2,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ! [X3] :
          ( ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_connsp_2(X3,sK0,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
          | v1_xboole_0(X3) )
      & m1_connsp_2(sK2,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f676,plain,(
    ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f673])).

fof(f673,plain,
    ( $false
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f50,f72,f389])).

fof(f389,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(X2)
        | ~ m1_connsp_2(X3,X2,X4)
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | ~ r1_tarski(k1_tops_1(X2,X3),k1_tops_1(sK0,sK2)) )
    | ~ spl5_11 ),
    inference(resolution,[],[f385,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f53,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f385,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,k1_tops_1(sK0,sK2)) )
    | ~ spl5_11 ),
    inference(resolution,[],[f384,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f384,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
        | ~ r2_hidden(X5,X4) )
    | ~ spl5_11 ),
    inference(resolution,[],[f288,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f288,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl5_11
  <=> v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f50,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f377,plain,
    ( ~ spl5_7
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl5_7
    | spl5_9 ),
    inference(subsumption_resolution,[],[f370,f186])).

fof(f186,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl5_7
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f370,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl5_9 ),
    inference(resolution,[],[f321,f49])).

fof(f321,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_tops_1(sK0,sK2),X6) )
    | spl5_9 ),
    inference(resolution,[],[f300,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f300,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ r1_tarski(k1_tops_1(sK0,sK2),X2) )
    | spl5_9 ),
    inference(resolution,[],[f292,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f292,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl5_9 ),
    inference(resolution,[],[f280,f68])).

fof(f280,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl5_9
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f335,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f333,f47])).

fof(f333,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f328,f49])).

fof(f328,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_10 ),
    inference(resolution,[],[f306,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(k1_tops_1(X0,X1),k1_tops_1(X0,k1_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f59,f76])).

fof(f76,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f306,plain,
    ( ~ sQ4_eqProxy(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | spl5_10 ),
    inference(resolution,[],[f284,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f76])).

fof(f284,plain,
    ( ~ sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl5_10
  <=> sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f289,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f251,f185,f106,f286,f282,f278])).

fof(f106,plain,
    ( spl5_2
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ sQ4_eqProxy(k1_tops_1(X0,X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f251,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f248,f186])).

fof(f248,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(resolution,[],[f236,f50])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
        | v1_xboole_0(k1_tops_1(sK0,X0))
        | ~ sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,X0))
        | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f235,f46])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,X0))
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
        | v1_xboole_0(k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,sK1)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f234,f47])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,X0))
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
        | v1_xboole_0(k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f232,f48])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,X0))
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
        | v1_xboole_0(k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f212,f45])).

fof(f212,plain,
    ( ! [X2,X1] :
        ( v2_struct_0(X1)
        | ~ sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(X1,X2)),k1_tops_1(X1,X2))
        | ~ r1_tarski(k1_tops_1(X1,X2),sK2)
        | v1_xboole_0(k1_tops_1(X1,X2))
        | ~ m1_connsp_2(X2,X1,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f208,f100])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X0),X0)
        | ~ r1_tarski(X0,sK2)
        | v1_xboole_0(X0) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X0),X0)
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X0),X0)
        | ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f168,f114])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X0),X0)
        | ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X0),X0)
        | ~ r1_tarski(X0,sK2)
        | ~ m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f111,f51])).

fof(f51,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK2)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f111,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X0),X0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f109,f47])).

fof(f109,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X0),X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f107,f46])).

fof(f107,plain,
    ( ! [X2,X0] :
        ( ~ v2_pre_topc(X0)
        | v3_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ sQ4_eqProxy(k1_tops_1(X0,X2),X2) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( m1_connsp_2(X1,sK0,X0)
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X1),X1) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f167,f45])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | m1_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X1),X1) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f166,f46])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | m1_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X1),X1) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f165,f47])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | m1_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X1),X1) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | m1_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sQ4_eqProxy(k1_tops_1(sK0,X1),X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f157,f111])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f55,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f202,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl5_7 ),
    inference(subsumption_resolution,[],[f200,f47])).

fof(f200,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f194,f49])).

fof(f194,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_7 ),
    inference(resolution,[],[f187,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f187,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f185])).

fof(f108,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f77,f106,f103])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ sQ4_eqProxy(k1_tops_1(X0,X2),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f57,f76])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:27:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.44  % (11411)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (11412)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.48  % (11415)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.49  % (11398)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (11421)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (11403)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (11400)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (11418)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (11414)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (11399)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (11413)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (11422)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (11411)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (11410)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (11409)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (11397)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (11419)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (11402)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (11420)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (11406)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (11408)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (11401)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f686,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f108,f202,f289,f335,f377,f676,f684])).
% 0.22/0.53  fof(f684,plain,(
% 0.22/0.53    ~spl5_1),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f680])).
% 0.22/0.53  fof(f680,plain,(
% 0.22/0.53    $false | ~spl5_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f47,f49,f104])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ( ! [X3,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) ) | ~spl5_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f103])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl5_1 <=> ! [X1,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ((! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f35,f34,f33])).
% 0.22/0.53  % (11402)Refutation not found, incomplete strategy% (11402)------------------------------
% 0.22/0.53  % (11402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11402)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11402)Memory used [KB]: 6140
% 0.22/0.53  % (11402)Time elapsed: 0.086 s
% 0.22/0.53  % (11402)------------------------------
% 0.22/0.53  % (11402)------------------------------
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f13])).
% 0.22/0.53  fof(f13,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f676,plain,(
% 0.22/0.53    ~spl5_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f673])).
% 0.22/0.53  fof(f673,plain,(
% 0.22/0.53    $false | ~spl5_11),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f50,f72,f389])).
% 0.22/0.53  fof(f389,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (v2_struct_0(X2) | ~m1_connsp_2(X3,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~r1_tarski(k1_tops_1(X2,X3),k1_tops_1(sK0,sK2))) ) | ~spl5_11),
% 0.22/0.53    inference(resolution,[],[f385,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f53,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.22/0.53  fof(f385,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,k1_tops_1(sK0,sK2))) ) | ~spl5_11),
% 0.22/0.53    inference(resolution,[],[f384,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f384,plain,(
% 0.22/0.53    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | ~r2_hidden(X5,X4)) ) | ~spl5_11),
% 0.22/0.53    inference(resolution,[],[f288,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.53  fof(f288,plain,(
% 0.22/0.53    v1_xboole_0(k1_tops_1(sK0,sK2)) | ~spl5_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f286])).
% 0.22/0.53  fof(f286,plain,(
% 0.22/0.53    spl5_11 <=> v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    m1_connsp_2(sK2,sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f377,plain,(
% 0.22/0.53    ~spl5_7 | spl5_9),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f376])).
% 0.22/0.53  fof(f376,plain,(
% 0.22/0.53    $false | (~spl5_7 | spl5_9)),
% 0.22/0.53    inference(subsumption_resolution,[],[f370,f186])).
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl5_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f185])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    spl5_7 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.53  fof(f370,plain,(
% 0.22/0.53    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | spl5_9),
% 0.22/0.53    inference(resolution,[],[f321,f49])).
% 0.22/0.53  fof(f321,plain,(
% 0.22/0.53    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,sK2),X6)) ) | spl5_9),
% 0.22/0.53    inference(resolution,[],[f300,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f300,plain,(
% 0.22/0.53    ( ! [X2] : (~r1_tarski(X2,u1_struct_0(sK0)) | ~r1_tarski(k1_tops_1(sK0,sK2),X2)) ) | spl5_9),
% 0.22/0.53    inference(resolution,[],[f292,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.53  fof(f292,plain,(
% 0.22/0.53    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl5_9),
% 0.22/0.53    inference(resolution,[],[f280,f68])).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f278])).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    spl5_9 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    spl5_10),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f334])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    $false | spl5_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f333,f47])).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | spl5_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f328,f49])).
% 0.22/0.53  fof(f328,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_10),
% 0.22/0.53    inference(resolution,[],[f306,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sQ4_eqProxy(k1_tops_1(X0,X1),k1_tops_1(X0,k1_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(equality_proxy_replacement,[],[f59,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.53    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.22/0.53  fof(f306,plain,(
% 0.22/0.53    ~sQ4_eqProxy(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k1_tops_1(sK0,sK2))) | spl5_10),
% 0.22/0.53    inference(resolution,[],[f284,f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sQ4_eqProxy(X1,X0) | ~sQ4_eqProxy(X0,X1)) )),
% 0.22/0.53    inference(equality_proxy_axiom,[],[f76])).
% 0.22/0.53  fof(f284,plain,(
% 0.22/0.53    ~sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2)) | spl5_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f282])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    spl5_10 <=> sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.53  fof(f289,plain,(
% 0.22/0.53    ~spl5_9 | ~spl5_10 | spl5_11 | ~spl5_2 | ~spl5_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f251,f185,f106,f286,f282,f278])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl5_2 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~sQ4_eqProxy(k1_tops_1(X0,X2),X2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    v1_xboole_0(k1_tops_1(sK0,sK2)) | ~sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2)) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_2 | ~spl5_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f248,f186])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | v1_xboole_0(k1_tops_1(sK0,sK2)) | ~sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2)) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_2),
% 0.22/0.53    inference(resolution,[],[f236,f50])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,X0),sK2) | v1_xboole_0(k1_tops_1(sK0,X0)) | ~sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,X0)) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f235,f46])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ( ! [X0] : (~sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,X0)) | ~r1_tarski(k1_tops_1(sK0,X0),sK2) | v1_xboole_0(k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f234,f47])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    ( ! [X0] : (~sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,X0)) | ~r1_tarski(k1_tops_1(sK0,X0),sK2) | v1_xboole_0(k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f232,f48])).
% 0.22/0.53  fof(f232,plain,(
% 0.22/0.53    ( ! [X0] : (~sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,X0)) | ~r1_tarski(k1_tops_1(sK0,X0),sK2) | v1_xboole_0(k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_2),
% 0.22/0.53    inference(resolution,[],[f212,f45])).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    ( ! [X2,X1] : (v2_struct_0(X1) | ~sQ4_eqProxy(k1_tops_1(sK0,k1_tops_1(X1,X2)),k1_tops_1(X1,X2)) | ~r1_tarski(k1_tops_1(X1,X2),sK2) | v1_xboole_0(k1_tops_1(X1,X2)) | ~m1_connsp_2(X2,X1,sK1) | ~m1_subset_1(sK1,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_2),
% 0.22/0.53    inference(resolution,[],[f208,f100])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ4_eqProxy(k1_tops_1(sK0,X0),X0) | ~r1_tarski(X0,sK2) | v1_xboole_0(X0)) ) | ~spl5_2),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f207])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ4_eqProxy(k1_tops_1(sK0,X0),X0) | ~sQ4_eqProxy(k1_tops_1(sK0,X0),X0) | ~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0)) ) | ~spl5_2),
% 0.22/0.53    inference(resolution,[],[f168,f114])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~sQ4_eqProxy(k1_tops_1(sK0,X0),X0) | ~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0)) ) | ~spl5_2),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ4_eqProxy(k1_tops_1(sK0,X0),X0) | ~r1_tarski(X0,sK2) | ~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0)) ) | ~spl5_2),
% 0.22/0.53    inference(resolution,[],[f111,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X3] : (~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ4_eqProxy(k1_tops_1(sK0,X0),X0)) ) | ~spl5_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f109,f47])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ4_eqProxy(k1_tops_1(sK0,X0),X0)) ) | ~spl5_2),
% 0.22/0.53    inference(resolution,[],[f107,f46])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~v2_pre_topc(X0) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~sQ4_eqProxy(k1_tops_1(X0,X2),X2)) ) | ~spl5_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f106])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_connsp_2(X1,sK0,X0) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ4_eqProxy(k1_tops_1(sK0,X1),X1)) ) | ~spl5_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f167,f45])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~sQ4_eqProxy(k1_tops_1(sK0,X1),X1)) ) | ~spl5_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f166,f46])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sQ4_eqProxy(k1_tops_1(sK0,X1),X1)) ) | ~spl5_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f165,f47])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sQ4_eqProxy(k1_tops_1(sK0,X1),X1)) ) | ~spl5_2),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f164])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ4_eqProxy(k1_tops_1(sK0,X1),X1)) ) | ~spl5_2),
% 0.22/0.53    inference(resolution,[],[f157,f111])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f55,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    spl5_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f201])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    $false | spl5_7),
% 0.22/0.53    inference(subsumption_resolution,[],[f200,f47])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | spl5_7),
% 0.22/0.53    inference(subsumption_resolution,[],[f194,f49])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_7),
% 0.22/0.53    inference(resolution,[],[f187,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | spl5_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f185])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl5_1 | spl5_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f77,f106,f103])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | ~sQ4_eqProxy(k1_tops_1(X0,X2),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(equality_proxy_replacement,[],[f57,f76])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (11411)------------------------------
% 0.22/0.53  % (11411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11411)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (11411)Memory used [KB]: 6524
% 0.22/0.53  % (11411)Time elapsed: 0.111 s
% 0.22/0.53  % (11411)------------------------------
% 0.22/0.53  % (11411)------------------------------
% 0.22/0.53  % (11405)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (11396)Success in time 0.178 s
%------------------------------------------------------------------------------
