%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 347 expanded)
%              Number of leaves         :   24 ( 143 expanded)
%              Depth                    :   16
%              Number of atoms          :  470 (2505 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f112,f116,f120,f218,f224,f232,f241])).

fof(f241,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl5_12 ),
    inference(subsumption_resolution,[],[f239,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    & m1_connsp_2(sK3,sK0,sK1)
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f36,f35,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
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

% (7079)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
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

% (7050)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
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

fof(f239,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_12 ),
    inference(subsumption_resolution,[],[f236,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f236,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_12 ),
    inference(resolution,[],[f233,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f233,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK3),sK3)
    | spl5_12 ),
    inference(resolution,[],[f217,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f217,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK3),k2_xboole_0(sK2,sK3))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl5_12
  <=> r1_tarski(k1_tops_1(sK0,sK3),k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f232,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl5_11 ),
    inference(subsumption_resolution,[],[f230,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f230,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_11 ),
    inference(subsumption_resolution,[],[f229,f46])).

fof(f229,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_11 ),
    inference(subsumption_resolution,[],[f228,f49])).

fof(f228,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_11 ),
    inference(resolution,[],[f213,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

% (7051)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f213,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK3),sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl5_11
  <=> v3_pre_topc(k1_tops_1(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f224,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f222,f46])).

fof(f222,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f219,f49])).

fof(f219,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_10 ),
    inference(resolution,[],[f209,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f209,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl5_10
  <=> m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f218,plain,
    ( ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f205,f92,f89,f215,f211,f207])).

fof(f89,plain,
    ( spl5_3
  <=> ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | ~ r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f92,plain,
    ( spl5_4
  <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f205,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK3),k2_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(k1_tops_1(sK0,sK3),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f204,f46])).

fof(f204,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK3),k2_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(k1_tops_1(sK0,sK3),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f201,f93])).

fof(f93,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f201,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK3),k2_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(k1_tops_1(sK0,sK3),sK0)
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f155,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
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
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f155,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl5_3 ),
    inference(resolution,[],[f153,f51])).

fof(f51,plain,(
    m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f152,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
        | v2_struct_0(sK0) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f151,f45])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f150,f46])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f133,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f133,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK1,u1_struct_0(X2))
        | ~ m1_connsp_2(X3,X2,sK1)
        | ~ r1_tarski(k1_tops_1(X2,X3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_3 ),
    inference(resolution,[],[f90,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f55,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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

fof(f90,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | ~ r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f120,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl5_6 ),
    inference(subsumption_resolution,[],[f118,f49])).

fof(f118,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_6 ),
    inference(resolution,[],[f111,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f111,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_6
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f116,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f114,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f114,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_5 ),
    inference(resolution,[],[f107,f63])).

fof(f107,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_5
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f112,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_4 ),
    inference(avatar_split_clause,[],[f101,f92,f109,f105])).

fof(f101,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl5_4 ),
    inference(resolution,[],[f97,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f97,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | spl5_4 ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f94,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f95,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f79,f92,f89])).

fof(f79,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X1)
      | ~ r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ) ),
    inference(resolution,[],[f77,f70])).

fof(f70,plain,(
    ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(subsumption_resolution,[],[f69,f48])).

fof(f69,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f68,f49])).

fof(f68,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f52,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f52,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X2,X1] :
      ( m1_connsp_2(X1,sK0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X2)
      | ~ r1_tarski(X2,k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f75,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

% (7053)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f74,f47])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | m1_connsp_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f73,f45])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | m1_connsp_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f72,f46])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_connsp_2(X1,sK0,X0) ) ),
    inference(resolution,[],[f56,f44])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (7058)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (7052)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (7074)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (7062)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (7058)Refutation not found, incomplete strategy% (7058)------------------------------
% 0.21/0.52  % (7058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7054)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (7059)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (7058)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7058)Memory used [KB]: 10618
% 0.21/0.52  % (7058)Time elapsed: 0.099 s
% 0.21/0.52  % (7058)------------------------------
% 0.21/0.52  % (7058)------------------------------
% 0.21/0.52  % (7052)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f95,f112,f116,f120,f218,f224,f232,f241])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    spl5_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f240])).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    $false | spl5_12),
% 0.21/0.53    inference(subsumption_resolution,[],[f239,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) & m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f36,f35,f34,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) & m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) & m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) & m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  % (7079)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  % (7050)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).
% 0.21/0.54  fof(f239,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | spl5_12),
% 0.21/0.54    inference(subsumption_resolution,[],[f236,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_12),
% 0.21/0.54    inference(resolution,[],[f233,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,sK3),sK3) | spl5_12),
% 0.21/0.54    inference(resolution,[],[f217,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,sK3),k2_xboole_0(sK2,sK3)) | spl5_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f215])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    spl5_12 <=> r1_tarski(k1_tops_1(sK0,sK3),k2_xboole_0(sK2,sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    spl5_11),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f231])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    $false | spl5_11),
% 0.21/0.54    inference(subsumption_resolution,[],[f230,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f230,plain,(
% 0.21/0.54    ~v2_pre_topc(sK0) | spl5_11),
% 0.21/0.54    inference(subsumption_resolution,[],[f229,f46])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_11),
% 0.21/0.54    inference(subsumption_resolution,[],[f228,f49])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_11),
% 0.21/0.54    inference(resolution,[],[f213,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.54  % (7051)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    ~v3_pre_topc(k1_tops_1(sK0,sK3),sK0) | spl5_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f211])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    spl5_11 <=> v3_pre_topc(k1_tops_1(sK0,sK3),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    spl5_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f223])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    $false | spl5_10),
% 0.21/0.54    inference(subsumption_resolution,[],[f222,f46])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | spl5_10),
% 0.21/0.54    inference(subsumption_resolution,[],[f219,f49])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_10),
% 0.21/0.54    inference(resolution,[],[f209,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    ~m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f207])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    spl5_10 <=> m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_3 | ~spl5_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f205,f92,f89,f215,f211,f207])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    spl5_3 <=> ! [X1] : (~r2_hidden(sK1,X1) | ~r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    spl5_4 <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,sK3),k2_xboole_0(sK2,sK3)) | ~v3_pre_topc(k1_tops_1(sK0,sK3),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_3 | ~spl5_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f204,f46])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,sK3),k2_xboole_0(sK2,sK3)) | ~v3_pre_topc(k1_tops_1(sK0,sK3),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_3 | ~spl5_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f201,f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f92])).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,sK3),k2_xboole_0(sK2,sK3)) | ~v3_pre_topc(k1_tops_1(sK0,sK3),sK0) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f155,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f153,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    m1_connsp_2(sK3,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))) ) | ~spl5_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f152,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | v2_struct_0(sK0)) ) | ~spl5_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f151,f45])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f150,f46])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f133,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~m1_subset_1(sK1,u1_struct_0(X2)) | ~m1_connsp_2(X3,X2,sK1) | ~r1_tarski(k1_tops_1(X2,X3),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f90,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f55,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK1,X1) | ~r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))) ) | ~spl5_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f89])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    spl5_6),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    $false | spl5_6),
% 0.21/0.54    inference(subsumption_resolution,[],[f118,f49])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_6),
% 0.21/0.54    inference(resolution,[],[f111,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ~r1_tarski(sK3,u1_struct_0(sK0)) | spl5_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f109])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl5_6 <=> r1_tarski(sK3,u1_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl5_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    $false | spl5_5),
% 0.21/0.54    inference(subsumption_resolution,[],[f114,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_5),
% 0.21/0.54    inference(resolution,[],[f107,f63])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl5_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl5_5 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ~spl5_5 | ~spl5_6 | spl5_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f101,f92,f109,f105])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ~r1_tarski(sK3,u1_struct_0(sK0)) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl5_4),
% 0.21/0.54    inference(resolution,[],[f97,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ~r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) | spl5_4),
% 0.21/0.54    inference(resolution,[],[f94,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f92])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    spl5_3 | ~spl5_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f79,f92,f89])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X1) | ~r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))) )),
% 0.21/0.54    inference(resolution,[],[f77,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f69,f48])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f68,f49])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(superposition,[],[f52,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(flattening,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X2,X1] : (m1_connsp_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X2) | ~r1_tarski(X2,k1_tops_1(sK0,X1))) )),
% 0.21/0.54    inference(resolution,[],[f75,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  % (7053)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1)) )),
% 0.21/0.54    inference(resolution,[],[f74,f47])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | m1_connsp_2(X1,sK0,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f73,f45])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | m1_connsp_2(X1,sK0,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f72,f46])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_connsp_2(X1,sK0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f56,f44])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (7052)------------------------------
% 0.21/0.54  % (7052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7052)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (7052)Memory used [KB]: 10874
% 0.21/0.54  % (7052)Time elapsed: 0.108 s
% 0.21/0.54  % (7052)------------------------------
% 0.21/0.54  % (7052)------------------------------
% 0.21/0.54  % (7060)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (7048)Success in time 0.181 s
%------------------------------------------------------------------------------
