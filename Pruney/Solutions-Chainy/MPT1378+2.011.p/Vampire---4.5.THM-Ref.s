%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 295 expanded)
%              Number of leaves         :   19 ( 122 expanded)
%              Depth                    :   14
%              Number of atoms          :  419 (2252 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f408,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f255,f272,f381,f385,f389,f407])).

fof(f407,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl6_7 ),
    inference(subsumption_resolution,[],[f405,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    & m1_connsp_2(sK3,sK0,sK1)
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                  & m1_connsp_2(X3,sK0,X1)
                  & m1_connsp_2(X2,sK0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                & m1_connsp_2(X3,sK0,X1)
                & m1_connsp_2(X2,sK0,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
              & m1_connsp_2(X3,sK0,sK1)
              & m1_connsp_2(X2,sK0,sK1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
            & m1_connsp_2(X3,sK0,sK1)
            & m1_connsp_2(X2,sK0,sK1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
          & m1_connsp_2(X3,sK0,sK1)
          & m1_connsp_2(sK2,sK0,sK1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
        & m1_connsp_2(X3,sK0,sK1)
        & m1_connsp_2(sK2,sK0,sK1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
      & m1_connsp_2(sK3,sK0,sK1)
      & m1_connsp_2(sK2,sK0,sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f405,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_7 ),
    inference(subsumption_resolution,[],[f398,f43])).

fof(f43,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f398,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_7 ),
    inference(resolution,[],[f394,f238])).

fof(f238,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f237,f40])).

fof(f40,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,X1)
      | r2_hidden(X1,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f236,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k1_tops_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f235,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | r2_hidden(X1,k1_tops_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f394,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl6_7 ),
    inference(resolution,[],[f380,f62])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f380,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl6_7
  <=> r2_hidden(sK1,k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f389,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | spl6_6 ),
    inference(subsumption_resolution,[],[f387,f39])).

fof(f387,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_6 ),
    inference(subsumption_resolution,[],[f386,f42])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f386,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl6_6 ),
    inference(resolution,[],[f376,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f376,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl6_6
  <=> m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f385,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl6_5 ),
    inference(subsumption_resolution,[],[f383,f39])).

fof(f383,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_5 ),
    inference(subsumption_resolution,[],[f382,f41])).

fof(f382,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl6_5 ),
    inference(resolution,[],[f372,f49])).

fof(f372,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl6_5
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f381,plain,
    ( ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_2 ),
    inference(avatar_split_clause,[],[f368,f252,f378,f374,f370])).

fof(f252,plain,
    ( spl6_2
  <=> r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f368,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_2 ),
    inference(superposition,[],[f361,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f361,plain,
    ( ~ r2_hidden(sK1,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | spl6_2 ),
    inference(subsumption_resolution,[],[f360,f42])).

fof(f360,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | spl6_2 ),
    inference(subsumption_resolution,[],[f352,f41])).

fof(f352,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | spl6_2 ),
    inference(resolution,[],[f345,f278])).

fof(f278,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
        | ~ r2_hidden(sK1,X1) )
    | spl6_2 ),
    inference(resolution,[],[f254,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f254,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f252])).

fof(f345,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f46,f39])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

fof(f272,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f270,f41])).

fof(f270,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f268,f42])).

fof(f268,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1 ),
    inference(resolution,[],[f250,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f250,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl6_1
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f255,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f245,f252,f248])).

fof(f245,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f244,f45])).

fof(f45,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f244,plain,(
    ! [X0] :
      ( m1_connsp_2(X0,sK0,sK1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f243,f40])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | m1_connsp_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f242,f37])).

fof(f242,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(X1,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f241,f39])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | m1_connsp_2(X1,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f48,f38])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:57:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (9250)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (9242)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (9236)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (9250)Refutation not found, incomplete strategy% (9250)------------------------------
% 0.22/0.52  % (9250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9250)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9250)Memory used [KB]: 10746
% 0.22/0.52  % (9250)Time elapsed: 0.063 s
% 0.22/0.52  % (9250)------------------------------
% 0.22/0.52  % (9250)------------------------------
% 0.22/0.52  % (9229)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (9230)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (9232)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (9233)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (9231)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (9228)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (9254)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (9253)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (9234)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (9235)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (9247)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (9252)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (9243)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (9237)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (9257)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (9244)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (9245)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (9245)Refutation not found, incomplete strategy% (9245)------------------------------
% 0.22/0.55  % (9245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9245)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9245)Memory used [KB]: 10618
% 0.22/0.55  % (9245)Time elapsed: 0.139 s
% 0.22/0.55  % (9245)------------------------------
% 0.22/0.55  % (9245)------------------------------
% 0.22/0.55  % (9251)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (9249)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (9241)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (9240)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (9238)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (9239)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (9256)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (9255)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (9246)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.57  % (9231)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (9248)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f408,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f255,f272,f381,f385,f389,f407])).
% 0.22/0.57  fof(f407,plain,(
% 0.22/0.57    spl6_7),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f406])).
% 0.22/0.57  fof(f406,plain,(
% 0.22/0.57    $false | spl6_7),
% 0.22/0.57    inference(subsumption_resolution,[],[f405,f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) & m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f25,f24,f23,f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) & m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) & m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) & m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f10])).
% 0.22/0.57  fof(f10,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,negated_conjecture,(
% 0.22/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 0.22/0.57    inference(negated_conjecture,[],[f8])).
% 0.22/0.57  fof(f8,conjecture,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).
% 0.22/0.57  fof(f405,plain,(
% 0.22/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_7),
% 0.22/0.57    inference(subsumption_resolution,[],[f398,f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    m1_connsp_2(sK2,sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f398,plain,(
% 0.22/0.57    ~m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_7),
% 0.22/0.57    inference(resolution,[],[f394,f238])).
% 0.22/0.57  fof(f238,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.57    inference(resolution,[],[f237,f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f237,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,X1) | r2_hidden(X1,k1_tops_1(sK0,X0))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f236,f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ~v2_struct_0(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f236,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f235,f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    l1_pre_topc(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f235,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | r2_hidden(X1,k1_tops_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.57    inference(resolution,[],[f47,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    v2_pre_topc(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.22/0.57  fof(f394,plain,(
% 0.22/0.57    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl6_7),
% 0.22/0.57    inference(resolution,[],[f380,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(rectify,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(flattening,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(nnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.57  fof(f380,plain,(
% 0.22/0.57    ~r2_hidden(sK1,k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))) | spl6_7),
% 0.22/0.57    inference(avatar_component_clause,[],[f378])).
% 0.22/0.57  fof(f378,plain,(
% 0.22/0.57    spl6_7 <=> r2_hidden(sK1,k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.57  fof(f389,plain,(
% 0.22/0.57    spl6_6),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f388])).
% 0.22/0.57  fof(f388,plain,(
% 0.22/0.57    $false | spl6_6),
% 0.22/0.57    inference(subsumption_resolution,[],[f387,f39])).
% 0.22/0.57  fof(f387,plain,(
% 0.22/0.57    ~l1_pre_topc(sK0) | spl6_6),
% 0.22/0.57    inference(subsumption_resolution,[],[f386,f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f386,plain,(
% 0.22/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl6_6),
% 0.22/0.57    inference(resolution,[],[f376,f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.22/0.57  fof(f376,plain,(
% 0.22/0.57    ~m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f374])).
% 0.22/0.57  fof(f374,plain,(
% 0.22/0.57    spl6_6 <=> m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.57  fof(f385,plain,(
% 0.22/0.57    spl6_5),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f384])).
% 0.22/0.57  fof(f384,plain,(
% 0.22/0.57    $false | spl6_5),
% 0.22/0.57    inference(subsumption_resolution,[],[f383,f39])).
% 0.22/0.57  fof(f383,plain,(
% 0.22/0.57    ~l1_pre_topc(sK0) | spl6_5),
% 0.22/0.57    inference(subsumption_resolution,[],[f382,f41])).
% 0.22/0.57  fof(f382,plain,(
% 0.22/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl6_5),
% 0.22/0.57    inference(resolution,[],[f372,f49])).
% 0.22/0.57  fof(f372,plain,(
% 0.22/0.57    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f370])).
% 0.22/0.57  fof(f370,plain,(
% 0.22/0.57    spl6_5 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.57  fof(f381,plain,(
% 0.22/0.57    ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f368,f252,f378,f374,f370])).
% 0.22/0.57  fof(f252,plain,(
% 0.22/0.57    spl6_2 <=> r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.57  fof(f368,plain,(
% 0.22/0.57    ~r2_hidden(sK1,k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))) | ~m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_2),
% 0.22/0.57    inference(superposition,[],[f361,f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(flattening,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.57  fof(f361,plain,(
% 0.22/0.57    ~r2_hidden(sK1,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))) | spl6_2),
% 0.22/0.57    inference(subsumption_resolution,[],[f360,f42])).
% 0.22/0.57  fof(f360,plain,(
% 0.22/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))) | spl6_2),
% 0.22/0.57    inference(subsumption_resolution,[],[f352,f41])).
% 0.22/0.57  fof(f352,plain,(
% 0.22/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))) | spl6_2),
% 0.22/0.57    inference(resolution,[],[f345,f278])).
% 0.22/0.57  fof(f278,plain,(
% 0.22/0.57    ( ! [X1] : (~r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) | ~r2_hidden(sK1,X1)) ) | spl6_2),
% 0.22/0.57    inference(resolution,[],[f254,f50])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.57  fof(f254,plain,(
% 0.22/0.57    ~r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) | spl6_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f252])).
% 0.22/0.57  fof(f345,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.57    inference(resolution,[],[f46,f39])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).
% 0.22/0.57  fof(f272,plain,(
% 0.22/0.57    spl6_1),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f271])).
% 0.22/0.57  fof(f271,plain,(
% 0.22/0.57    $false | spl6_1),
% 0.22/0.57    inference(subsumption_resolution,[],[f270,f41])).
% 0.22/0.57  fof(f270,plain,(
% 0.22/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_1),
% 0.22/0.57    inference(subsumption_resolution,[],[f268,f42])).
% 0.22/0.57  fof(f268,plain,(
% 0.22/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_1),
% 0.22/0.57    inference(resolution,[],[f250,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(flattening,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.22/0.57  fof(f250,plain,(
% 0.22/0.57    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f248])).
% 0.22/0.57  fof(f248,plain,(
% 0.22/0.57    spl6_1 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.57  fof(f255,plain,(
% 0.22/0.57    ~spl6_1 | ~spl6_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f245,f252,f248])).
% 0.22/0.57  fof(f245,plain,(
% 0.22/0.57    ~r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.57    inference(resolution,[],[f244,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f244,plain,(
% 0.22/0.57    ( ! [X0] : (m1_connsp_2(X0,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.57    inference(resolution,[],[f243,f40])).
% 0.22/0.57  fof(f243,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | m1_connsp_2(X1,sK0,X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f242,f37])).
% 0.22/0.57  fof(f242,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(X1,sK0,X0) | v2_struct_0(sK0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f241,f39])).
% 0.22/0.57  fof(f241,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | m1_connsp_2(X1,sK0,X0) | v2_struct_0(sK0)) )),
% 0.22/0.57    inference(resolution,[],[f48,f38])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (9231)------------------------------
% 0.22/0.57  % (9231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (9231)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (9231)Memory used [KB]: 11001
% 0.22/0.57  % (9231)Time elapsed: 0.145 s
% 0.22/0.57  % (9231)------------------------------
% 0.22/0.57  % (9231)------------------------------
% 0.22/0.58  % (9223)Success in time 0.211 s
%------------------------------------------------------------------------------
