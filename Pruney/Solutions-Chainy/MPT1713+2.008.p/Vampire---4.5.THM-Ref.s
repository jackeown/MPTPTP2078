%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 200 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  369 (1158 expanded)
%              Number of equality atoms :   17 (  28 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f439,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f81,f82,f254,f423,f427,f437])).

fof(f437,plain,
    ( ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f435,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( r1_tsep_1(sK2,sK1)
      | r1_tsep_1(sK1,sK2) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_tsep_1(X2,X1)
                  | r1_tsep_1(X1,X2) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( r1_tsep_1(X2,X1)
              | r1_tsep_1(X1,X2) )
            & m1_pre_topc(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( r1_tsep_1(X2,sK1)
            | r1_tsep_1(sK1,X2) )
          & m1_pre_topc(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ( r1_tsep_1(X2,sK1)
          | r1_tsep_1(sK1,X2) )
        & m1_pre_topc(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ( r1_tsep_1(sK2,sK1)
        | r1_tsep_1(sK1,sK2) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

% (17326)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (17340)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f435,plain,
    ( v2_struct_0(sK1)
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f429,f235])).

fof(f235,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl3_11
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f429,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f149,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f149,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_5
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f427,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | spl3_5
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f425,f40])).

fof(f40,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f425,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ spl3_1
    | ~ spl3_3
    | spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f424,f74])).

fof(f74,plain,
    ( l1_pre_topc(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_3
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f424,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ spl3_1
    | spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f61,f337])).

fof(f337,plain,
    ( ! [X60] :
        ( ~ r1_tsep_1(sK1,X60)
        | ~ l1_pre_topc(X60)
        | ~ m1_pre_topc(sK1,X60) )
    | spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f336,f235])).

fof(f336,plain,
    ( ! [X60] :
        ( ~ r1_tsep_1(sK1,X60)
        | ~ l1_struct_0(sK1)
        | ~ l1_pre_topc(X60)
        | ~ m1_pre_topc(sK1,X60) )
    | spl3_5 ),
    inference(subsumption_resolution,[],[f313,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f313,plain,
    ( ! [X60] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r1_tsep_1(sK1,X60)
        | ~ l1_struct_0(sK1)
        | ~ l1_pre_topc(X60)
        | ~ m1_pre_topc(sK1,X60) )
    | spl3_5 ),
    inference(superposition,[],[f150,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = u1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f185,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f185,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = u1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f93,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f47,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | k1_xboole_0 = u1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f89,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ r1_tarski(X0,u1_struct_0(X1))
      | k1_xboole_0 = X0
      | ~ r1_tsep_1(X2,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X2) ) ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f150,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f61,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_1
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f423,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f421,f40])).

fof(f421,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f419,f74])).

fof(f419,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ spl3_2
    | spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f413,f65])).

fof(f65,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_2
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f413,plain,
    ( ! [X61] :
        ( ~ r1_tsep_1(X61,sK1)
        | ~ l1_pre_topc(X61)
        | ~ m1_pre_topc(sK1,X61) )
    | spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f412,f235])).

fof(f412,plain,
    ( ! [X61] :
        ( ~ r1_tsep_1(X61,sK1)
        | ~ l1_struct_0(sK1)
        | ~ l1_pre_topc(X61)
        | ~ m1_pre_topc(sK1,X61) )
    | spl3_5 ),
    inference(subsumption_resolution,[],[f389,f42])).

fof(f389,plain,
    ( ! [X61] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r1_tsep_1(X61,sK1)
        | ~ l1_struct_0(sK1)
        | ~ l1_pre_topc(X61)
        | ~ m1_pre_topc(sK1,X61) )
    | spl3_5 ),
    inference(superposition,[],[f150,f256])).

fof(f256,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = u1_struct_0(X3)
      | ~ r1_tsep_1(X4,X3)
      | ~ l1_struct_0(X3)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X3,X4) ) ),
    inference(resolution,[],[f95,f56])).

fof(f95,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
      | k1_xboole_0 = u1_struct_0(X2)
      | ~ r1_tsep_1(X4,X3)
      | ~ l1_struct_0(X3)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X2,X4) ) ),
    inference(subsumption_resolution,[],[f94,f45])).

fof(f94,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
      | k1_xboole_0 = u1_struct_0(X2)
      | ~ r1_tsep_1(X4,X3)
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X2,X4) ) ),
    inference(resolution,[],[f89,f85])).

fof(f254,plain,
    ( ~ spl3_4
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f252,f79])).

fof(f79,plain,
    ( l1_pre_topc(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f252,plain,
    ( ~ l1_pre_topc(sK1)
    | spl3_11 ),
    inference(resolution,[],[f236,f45])).

fof(f236,plain,
    ( ~ l1_struct_0(sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f234])).

fof(f82,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f71,f73])).

fof(f71,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f68,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f39])).

fof(f39,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f70,f77])).

fof(f70,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f67,f35])).

fof(f67,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f37])).

fof(f37,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f41,f63,f59])).

fof(f41,plain,
    ( r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:37:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (17329)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (17348)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (17329)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (17328)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (17331)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (17336)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (17349)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (17336)Refutation not found, incomplete strategy% (17336)------------------------------
% 0.22/0.52  % (17336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17339)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (17343)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (17327)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (17331)Refutation not found, incomplete strategy% (17331)------------------------------
% 0.22/0.52  % (17331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17331)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17331)Memory used [KB]: 10618
% 0.22/0.52  % (17331)Time elapsed: 0.099 s
% 0.22/0.52  % (17331)------------------------------
% 0.22/0.52  % (17331)------------------------------
% 0.22/0.52  % (17346)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (17347)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (17336)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17336)Memory used [KB]: 10618
% 0.22/0.53  % (17336)Time elapsed: 0.100 s
% 0.22/0.53  % (17336)------------------------------
% 0.22/0.53  % (17336)------------------------------
% 0.22/0.53  % (17337)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (17335)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (17342)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (17345)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f439,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f66,f81,f82,f254,f423,f427,f437])).
% 0.22/0.53  fof(f437,plain,(
% 0.22/0.53    ~spl3_5 | ~spl3_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f436])).
% 0.22/0.53  fof(f436,plain,(
% 0.22/0.53    $false | (~spl3_5 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f435,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ~v2_struct_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    (((r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27,f26,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : ((r1_tsep_1(X2,sK1) | r1_tsep_1(sK1,X2)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ? [X2] : ((r1_tsep_1(X2,sK1) | r1_tsep_1(sK1,X2)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => ((r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  % (17326)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (17340)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).
% 0.22/0.53  fof(f435,plain,(
% 0.22/0.53    v2_struct_0(sK1) | (~spl3_5 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f429,f235])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    l1_struct_0(sK1) | ~spl3_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f234])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    spl3_11 <=> l1_struct_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.53  fof(f429,plain,(
% 0.22/0.53    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_5),
% 0.22/0.53    inference(resolution,[],[f149,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK1)) | ~spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f148])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl3_5 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f427,plain,(
% 0.22/0.53    ~spl3_1 | ~spl3_3 | spl3_5 | ~spl3_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f426])).
% 0.22/0.53  fof(f426,plain,(
% 0.22/0.53    $false | (~spl3_1 | ~spl3_3 | spl3_5 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f425,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    m1_pre_topc(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f425,plain,(
% 0.22/0.53    ~m1_pre_topc(sK1,sK2) | (~spl3_1 | ~spl3_3 | spl3_5 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f424,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    l1_pre_topc(sK2) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    spl3_3 <=> l1_pre_topc(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f424,plain,(
% 0.22/0.53    ~l1_pre_topc(sK2) | ~m1_pre_topc(sK1,sK2) | (~spl3_1 | spl3_5 | ~spl3_11)),
% 0.22/0.53    inference(resolution,[],[f61,f337])).
% 0.22/0.53  fof(f337,plain,(
% 0.22/0.53    ( ! [X60] : (~r1_tsep_1(sK1,X60) | ~l1_pre_topc(X60) | ~m1_pre_topc(sK1,X60)) ) | (spl3_5 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f336,f235])).
% 0.22/0.53  fof(f336,plain,(
% 0.22/0.53    ( ! [X60] : (~r1_tsep_1(sK1,X60) | ~l1_struct_0(sK1) | ~l1_pre_topc(X60) | ~m1_pre_topc(sK1,X60)) ) | spl3_5),
% 0.22/0.53    inference(subsumption_resolution,[],[f313,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f313,plain,(
% 0.22/0.53    ( ! [X60] : (~v1_xboole_0(k1_xboole_0) | ~r1_tsep_1(sK1,X60) | ~l1_struct_0(sK1) | ~l1_pre_topc(X60) | ~m1_pre_topc(sK1,X60)) ) | spl3_5),
% 0.22/0.53    inference(superposition,[],[f150,f192])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = u1_struct_0(X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f185,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = u1_struct_0(X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f93,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f47,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | k1_xboole_0 = u1_struct_0(X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.53    inference(resolution,[],[f89,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X1)) | k1_xboole_0 = X0 | ~r1_tsep_1(X2,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X2)) )),
% 0.22/0.53    inference(resolution,[],[f55,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    ~v1_xboole_0(u1_struct_0(sK1)) | spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f148])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    r1_tsep_1(sK1,sK2) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl3_1 <=> r1_tsep_1(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f423,plain,(
% 0.22/0.53    ~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f422])).
% 0.22/0.53  fof(f422,plain,(
% 0.22/0.53    $false | (~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f421,f40])).
% 0.22/0.53  fof(f421,plain,(
% 0.22/0.53    ~m1_pre_topc(sK1,sK2) | (~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f419,f74])).
% 0.22/0.53  fof(f419,plain,(
% 0.22/0.53    ~l1_pre_topc(sK2) | ~m1_pre_topc(sK1,sK2) | (~spl3_2 | spl3_5 | ~spl3_11)),
% 0.22/0.53    inference(resolution,[],[f413,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    r1_tsep_1(sK2,sK1) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl3_2 <=> r1_tsep_1(sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f413,plain,(
% 0.22/0.53    ( ! [X61] : (~r1_tsep_1(X61,sK1) | ~l1_pre_topc(X61) | ~m1_pre_topc(sK1,X61)) ) | (spl3_5 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f412,f235])).
% 0.22/0.53  fof(f412,plain,(
% 0.22/0.53    ( ! [X61] : (~r1_tsep_1(X61,sK1) | ~l1_struct_0(sK1) | ~l1_pre_topc(X61) | ~m1_pre_topc(sK1,X61)) ) | spl3_5),
% 0.22/0.53    inference(subsumption_resolution,[],[f389,f42])).
% 0.22/0.53  fof(f389,plain,(
% 0.22/0.53    ( ! [X61] : (~v1_xboole_0(k1_xboole_0) | ~r1_tsep_1(X61,sK1) | ~l1_struct_0(sK1) | ~l1_pre_topc(X61) | ~m1_pre_topc(sK1,X61)) ) | spl3_5),
% 0.22/0.53    inference(superposition,[],[f150,f256])).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    ( ! [X4,X3] : (k1_xboole_0 = u1_struct_0(X3) | ~r1_tsep_1(X4,X3) | ~l1_struct_0(X3) | ~l1_pre_topc(X4) | ~m1_pre_topc(X3,X4)) )),
% 0.22/0.53    inference(resolution,[],[f95,f56])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (~r1_tarski(u1_struct_0(X2),u1_struct_0(X3)) | k1_xboole_0 = u1_struct_0(X2) | ~r1_tsep_1(X4,X3) | ~l1_struct_0(X3) | ~l1_pre_topc(X4) | ~m1_pre_topc(X2,X4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f94,f45])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (~r1_tarski(u1_struct_0(X2),u1_struct_0(X3)) | k1_xboole_0 = u1_struct_0(X2) | ~r1_tsep_1(X4,X3) | ~l1_struct_0(X3) | ~l1_struct_0(X4) | ~l1_pre_topc(X4) | ~m1_pre_topc(X2,X4)) )),
% 0.22/0.53    inference(resolution,[],[f89,f85])).
% 0.22/0.53  fof(f254,plain,(
% 0.22/0.53    ~spl3_4 | spl3_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f253])).
% 0.22/0.53  fof(f253,plain,(
% 0.22/0.53    $false | (~spl3_4 | spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f252,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    l1_pre_topc(sK1) | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl3_4 <=> l1_pre_topc(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    ~l1_pre_topc(sK1) | spl3_11),
% 0.22/0.53    inference(resolution,[],[f236,f45])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ~l1_struct_0(sK1) | spl3_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f234])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f71,f73])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    l1_pre_topc(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f68,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(resolution,[],[f46,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    m1_pre_topc(sK2,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f70,f77])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    l1_pre_topc(sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f67,f35])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(resolution,[],[f46,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    m1_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl3_1 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f63,f59])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (17329)------------------------------
% 0.22/0.53  % (17329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17329)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (17329)Memory used [KB]: 6268
% 0.22/0.53  % (17329)Time elapsed: 0.101 s
% 0.22/0.53  % (17329)------------------------------
% 0.22/0.53  % (17329)------------------------------
% 0.22/0.54  % (17324)Success in time 0.169 s
%------------------------------------------------------------------------------
