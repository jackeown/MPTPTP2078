%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:51 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 149 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  415 ( 795 expanded)
%              Number of equality atoms :   50 (  58 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f76,f80,f84,f88,f102,f128,f156])).

fof(f156,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f146,f126,f100,f74,f70,f82,f78])).

fof(f78,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f82,plain,
    ( spl7_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f70,plain,
    ( spl7_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f74,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f100,plain,
    ( spl7_7
  <=> r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f126,plain,
    ( spl7_8
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f146,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(sK1,sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_7
    | ~ spl7_8 ),
    inference(resolution,[],[f138,f101])).

fof(f101,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f138,plain,
    ( ! [X4,X2,X3] :
        ( r2_hidden(k1_setfam_1(k2_tarski(X4,X2)),k1_tops_2(sK0,X2,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X4,X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_8 ),
    inference(resolution,[],[f133,f93])).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f58,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

% (13486)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f133,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2)) )
    | ~ spl7_8 ),
    inference(resolution,[],[f132,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1))
        | r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1))
        | r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_8 ),
    inference(superposition,[],[f127,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f127,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( ~ spl7_6
    | spl7_8
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f122,f86,f126,f86])).

fof(f86,plain,
    ( spl7_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f122,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_6 ),
    inference(superposition,[],[f117,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X2),k1_tops_2(sK0,X2,X1)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f92,f87])).

fof(f87,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f92,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f61,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(f61,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2))
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),X3)
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | k1_tops_2(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | k9_subset_1(u1_struct_0(X0),X8,X1) != X7
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | k1_tops_2(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ( ( ! [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3)
                              | ~ r2_hidden(X5,X2)
                              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
                        & ( ( sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1)
                            & r2_hidden(sK5(X0,X1,X2,X3),X2)
                            & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0))) )
                          | r2_hidden(sK4(X0,X1,X2,X3),X3) )
                        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X7] :
                          ( ( ( r2_hidden(X7,X3)
                              | ! [X8] :
                                  ( k9_subset_1(u1_struct_0(X0),X8,X1) != X7
                                  | ~ r2_hidden(X8,X2)
                                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7
                                & r2_hidden(sK6(X0,X1,X2,X7),X2)
                                & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X7,X3) ) )
                          | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( k9_subset_1(u1_struct_0(X0),X6,X1) = X4
                & r2_hidden(X6,X2)
                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
     => ( ( ! [X5] :
              ( k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3)
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3)
              & r2_hidden(X6,X2)
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3)
          & r2_hidden(X6,X2)
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1)
        & r2_hidden(sK5(X0,X1,X2,X3),X2)
        & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( k9_subset_1(u1_struct_0(X0),X9,X1) = X7
          & r2_hidden(X9,X2)
          & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7
        & r2_hidden(sK6(X0,X1,X2,X7),X2)
        & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                | ~ r2_hidden(X5,X2)
                                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | ~ r2_hidden(X4,X3) )
                          & ( ? [X6] :
                                ( k9_subset_1(u1_struct_0(X0),X6,X1) = X4
                                & r2_hidden(X6,X2)
                                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X7] :
                          ( ( ( r2_hidden(X7,X3)
                              | ! [X8] :
                                  ( k9_subset_1(u1_struct_0(X0),X8,X1) != X7
                                  | ~ r2_hidden(X8,X2)
                                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ? [X9] :
                                  ( k9_subset_1(u1_struct_0(X0),X9,X1) = X7
                                  & r2_hidden(X9,X2)
                                  & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X7,X3) ) )
                          | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                | ~ r2_hidden(X5,X2)
                                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | ~ r2_hidden(X4,X3) )
                          & ( ? [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                & r2_hidden(X5,X2)
                                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X4] :
                          ( ( ( r2_hidden(X4,X3)
                              | ! [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                  | ~ r2_hidden(X5,X2)
                                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ? [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                  & r2_hidden(X5,X2)
                                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X4,X3) ) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tops_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                | ~ r2_hidden(X5,X2)
                                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | ~ r2_hidden(X4,X3) )
                          & ( ? [X5] :
                                ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                & r2_hidden(X5,X2)
                                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                            | r2_hidden(X4,X3) )
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                    & ( ! [X4] :
                          ( ( ( r2_hidden(X4,X3)
                              | ! [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                                  | ~ r2_hidden(X5,X2)
                                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                            & ( ? [X5] :
                                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                                  & r2_hidden(X5,X2)
                                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                              | ~ r2_hidden(X4,X3) ) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                      | k1_tops_2(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
                 => ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
                       => ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_2)).

fof(f102,plain,
    ( ~ spl7_4
    | ~ spl7_7
    | spl7_1 ),
    inference(avatar_split_clause,[],[f97,f66,f100,f78])).

fof(f66,plain,
    ( spl7_1
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f97,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1 ),
    inference(superposition,[],[f67,f59])).

fof(f67,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f88,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f35,f86])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))
    & r2_hidden(sK1,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3))
                & r2_hidden(X1,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3))
              & r2_hidden(sK1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3))
            & r2_hidden(sK1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3))
          & r2_hidden(sK1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3))
        & r2_hidden(sK1,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))
      & r2_hidden(sK1,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ( r2_hidden(X1,X3)
                     => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                 => ( r2_hidden(X1,X3)
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_2)).

fof(f84,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f36,f82])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f38,f74])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f40,f66])).

fof(f40,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n011.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 16:24:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.49  % (13480)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (13474)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (13496)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.51  % (13485)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.52  % (13494)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.52  % (13476)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.52  % (13473)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.52  % (13482)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (13470)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (13497)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (13492)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.53  % (13478)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.53  % (13469)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.53  % (13483)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.53  % (13468)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (13477)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.53  % (13489)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (13475)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (13491)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.53  % (13488)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.53  % (13491)Refutation not found, incomplete strategy% (13491)------------------------------
% 0.19/0.53  % (13491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (13498)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  % (13493)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.54  % (13472)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.54  % (13491)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (13491)Memory used [KB]: 10746
% 0.19/0.54  % (13491)Time elapsed: 0.136 s
% 0.19/0.54  % (13491)------------------------------
% 0.19/0.54  % (13491)------------------------------
% 0.19/0.54  % (13471)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.54  % (13481)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.54  % (13495)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.54  % (13479)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.55  % (13487)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.55  % (13488)Refutation found. Thanks to Tanya!
% 0.19/0.55  % SZS status Theorem for theBenchmark
% 0.19/0.55  % SZS output start Proof for theBenchmark
% 0.19/0.55  fof(f157,plain,(
% 0.19/0.55    $false),
% 0.19/0.55    inference(avatar_sat_refutation,[],[f68,f72,f76,f80,f84,f88,f102,f128,f156])).
% 0.19/0.55  fof(f156,plain,(
% 0.19/0.55    ~spl7_4 | ~spl7_5 | ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_8),
% 0.19/0.55    inference(avatar_split_clause,[],[f146,f126,f100,f74,f70,f82,f78])).
% 0.19/0.55  fof(f78,plain,(
% 0.19/0.55    spl7_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.19/0.55  fof(f82,plain,(
% 0.19/0.55    spl7_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.19/0.55  fof(f70,plain,(
% 0.19/0.55    spl7_2 <=> r2_hidden(sK1,sK3)),
% 0.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.19/0.55  fof(f74,plain,(
% 0.19/0.55    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.19/0.55  fof(f100,plain,(
% 0.19/0.55    spl7_7 <=> r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3))),
% 0.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.19/0.55  fof(f126,plain,(
% 0.19/0.55    spl7_8 <=> ! [X1,X0,X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0)) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.19/0.55  fof(f146,plain,(
% 0.19/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_7 | ~spl7_8)),
% 0.19/0.55    inference(resolution,[],[f138,f101])).
% 0.19/0.55  fof(f101,plain,(
% 0.19/0.55    ~r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3)) | spl7_7),
% 0.19/0.55    inference(avatar_component_clause,[],[f100])).
% 0.19/0.55  fof(f138,plain,(
% 0.19/0.55    ( ! [X4,X2,X3] : (r2_hidden(k1_setfam_1(k2_tarski(X4,X2)),k1_tops_2(sK0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_8),
% 0.19/0.55    inference(resolution,[],[f133,f93])).
% 0.19/0.55  fof(f93,plain,(
% 0.19/0.55    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 0.19/0.55    inference(superposition,[],[f58,f52])).
% 0.19/0.55  fof(f52,plain,(
% 0.19/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f2])).
% 0.19/0.55  fof(f2,axiom,(
% 0.19/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.19/0.55  fof(f58,plain,(
% 0.19/0.55    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.19/0.55    inference(definition_unfolding,[],[f51,f53])).
% 0.19/0.55  fof(f53,plain,(
% 0.19/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.19/0.55    inference(cnf_transformation,[],[f4])).
% 0.19/0.55  % (13486)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.55  fof(f4,axiom,(
% 0.19/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.55  fof(f51,plain,(
% 0.19/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f1])).
% 0.19/0.55  fof(f1,axiom,(
% 0.19/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.19/0.55  fof(f133,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2))) ) | ~spl7_8),
% 0.19/0.55    inference(resolution,[],[f132,f54])).
% 0.19/0.55  fof(f54,plain,(
% 0.19/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f17])).
% 0.19/0.55  fof(f17,plain,(
% 0.19/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.55    inference(ennf_transformation,[],[f12])).
% 0.19/0.55  fof(f12,plain,(
% 0.19/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.19/0.55    inference(unused_predicate_definition_removal,[],[f5])).
% 0.19/0.55  fof(f5,axiom,(
% 0.19/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.55  fof(f132,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) | r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_8),
% 0.19/0.55    inference(duplicate_literal_removal,[],[f131])).
% 0.19/0.55  fof(f131,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) | r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_8),
% 0.19/0.55    inference(superposition,[],[f127,f59])).
% 0.19/0.55  fof(f59,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.19/0.55    inference(definition_unfolding,[],[f55,f53])).
% 0.19/0.55  fof(f55,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.19/0.55    inference(cnf_transformation,[],[f18])).
% 0.19/0.55  fof(f18,plain,(
% 0.19/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.55    inference(ennf_transformation,[],[f3])).
% 0.19/0.55  fof(f3,axiom,(
% 0.19/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.19/0.55  fof(f127,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0)) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_8),
% 0.19/0.55    inference(avatar_component_clause,[],[f126])).
% 0.19/0.55  fof(f128,plain,(
% 0.19/0.55    ~spl7_6 | spl7_8 | ~spl7_6),
% 0.19/0.55    inference(avatar_split_clause,[],[f122,f86,f126,f86])).
% 0.19/0.55  fof(f86,plain,(
% 0.19/0.55    spl7_6 <=> l1_pre_topc(sK0)),
% 0.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.19/0.55  fof(f122,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2)) | ~l1_pre_topc(sK0)) ) | ~spl7_6),
% 0.19/0.55    inference(duplicate_literal_removal,[],[f121])).
% 0.19/0.55  fof(f121,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl7_6),
% 0.19/0.55    inference(superposition,[],[f117,f41])).
% 0.19/0.55  fof(f41,plain,(
% 0.19/0.55    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f15])).
% 0.19/0.55  fof(f15,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(ennf_transformation,[],[f7])).
% 0.19/0.55  fof(f7,axiom,(
% 0.19/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.19/0.55  fof(f117,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X2),k1_tops_2(sK0,X2,X1))) ) | ~spl7_6),
% 0.19/0.55    inference(resolution,[],[f92,f87])).
% 0.19/0.55  fof(f87,plain,(
% 0.19/0.55    l1_pre_topc(sK0) | ~spl7_6),
% 0.19/0.55    inference(avatar_component_clause,[],[f86])).
% 0.19/0.55  fof(f92,plain,(
% 0.19/0.55    ( ! [X2,X0,X8,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2))) )),
% 0.19/0.55    inference(subsumption_resolution,[],[f61,f56])).
% 0.19/0.55  fof(f56,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f20])).
% 0.19/0.55  fof(f20,plain,(
% 0.19/0.55    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(flattening,[],[f19])).
% 0.19/0.55  fof(f19,plain,(
% 0.19/0.55    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.19/0.55    inference(ennf_transformation,[],[f9])).
% 0.19/0.55  fof(f9,axiom,(
% 0.19/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).
% 0.19/0.55  fof(f61,plain,(
% 0.19/0.55    ( ! [X2,X0,X8,X1] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2)) | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | ~m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.55    inference(equality_resolution,[],[f60])).
% 0.19/0.55  fof(f60,plain,(
% 0.19/0.55    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),X3) | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | k1_tops_2(X0,X1,X2) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.55    inference(equality_resolution,[],[f45])).
% 0.19/0.55  fof(f45,plain,(
% 0.19/0.55    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | k1_tops_2(X0,X1,X2) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f34])).
% 0.19/0.55  fof(f34,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & ((sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1) & r2_hidden(sK5(X0,X1,X2,X3),X2) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1,X2,X3),X3)) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X7] : (((r2_hidden(X7,X3) | ! [X8] : (k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7 & r2_hidden(sK6(X0,X1,X2,X7),X2) & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X7,X3))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).
% 0.19/0.55  fof(f31,plain,(
% 0.19/0.55    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = X4 & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) => ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3) & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1,X2,X3),X3)) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f32,plain,(
% 0.19/0.55    ! [X3,X2,X1,X0] : (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3) & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) => (sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1) & r2_hidden(sK5(X0,X1,X2,X3),X2) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f33,plain,(
% 0.19/0.55    ! [X7,X2,X1,X0] : (? [X9] : (k9_subset_1(u1_struct_0(X0),X9,X1) = X7 & r2_hidden(X9,X2) & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7 & r2_hidden(sK6(X0,X1,X2,X7),X2) & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f30,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = X4 & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X7] : (((r2_hidden(X7,X3) | ! [X8] : (k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X9] : (k9_subset_1(u1_struct_0(X0),X9,X1) = X7 & r2_hidden(X9,X2) & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X7,X3))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(rectify,[],[f29])).
% 0.19/0.55  fof(f29,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X4] : (((r2_hidden(X4,X3) | ! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(flattening,[],[f28])).
% 0.19/0.55  fof(f28,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : (((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X4] : (((r2_hidden(X4,X3) | ! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(nnf_transformation,[],[f16])).
% 0.19/0.55  fof(f16,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : ((r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(ennf_transformation,[],[f8])).
% 0.19/0.55  fof(f8,axiom,(
% 0.19/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) => (k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) => (r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))))))))))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_2)).
% 0.19/0.55  fof(f102,plain,(
% 0.19/0.55    ~spl7_4 | ~spl7_7 | spl7_1),
% 0.19/0.55    inference(avatar_split_clause,[],[f97,f66,f100,f78])).
% 0.19/0.55  fof(f66,plain,(
% 0.19/0.55    spl7_1 <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))),
% 0.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.19/0.55  fof(f97,plain,(
% 0.19/0.55    ~r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_1),
% 0.19/0.55    inference(superposition,[],[f67,f59])).
% 0.19/0.55  fof(f67,plain,(
% 0.19/0.55    ~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) | spl7_1),
% 0.19/0.55    inference(avatar_component_clause,[],[f66])).
% 0.19/0.55  fof(f88,plain,(
% 0.19/0.55    spl7_6),
% 0.19/0.55    inference(avatar_split_clause,[],[f35,f86])).
% 0.19/0.55  fof(f35,plain,(
% 0.19/0.55    l1_pre_topc(sK0)),
% 0.19/0.55    inference(cnf_transformation,[],[f27])).
% 0.19/0.55  fof(f27,plain,(
% 0.19/0.55    (((~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) & r2_hidden(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.19/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26,f25,f24,f23])).
% 0.19/0.55  fof(f23,plain,(
% 0.19/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f24,plain,(
% 0.19/0.55    ? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f25,plain,(
% 0.19/0.55    ? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f26,plain,(
% 0.19/0.55    ? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) & r2_hidden(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f14,plain,(
% 0.19/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.19/0.55    inference(flattening,[],[f13])).
% 0.19/0.55  fof(f13,plain,(
% 0.19/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.19/0.55    inference(ennf_transformation,[],[f11])).
% 0.19/0.55  fof(f11,negated_conjecture,(
% 0.19/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 0.19/0.55    inference(negated_conjecture,[],[f10])).
% 0.19/0.55  fof(f10,conjecture,(
% 0.19/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_2)).
% 0.19/0.55  fof(f84,plain,(
% 0.19/0.55    spl7_5),
% 0.19/0.55    inference(avatar_split_clause,[],[f36,f82])).
% 0.19/0.55  fof(f36,plain,(
% 0.19/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.55    inference(cnf_transformation,[],[f27])).
% 0.19/0.55  fof(f80,plain,(
% 0.19/0.55    spl7_4),
% 0.19/0.55    inference(avatar_split_clause,[],[f37,f78])).
% 0.19/0.55  fof(f37,plain,(
% 0.19/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.55    inference(cnf_transformation,[],[f27])).
% 0.19/0.55  fof(f76,plain,(
% 0.19/0.55    spl7_3),
% 0.19/0.55    inference(avatar_split_clause,[],[f38,f74])).
% 0.19/0.55  fof(f38,plain,(
% 0.19/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.55    inference(cnf_transformation,[],[f27])).
% 0.19/0.55  fof(f72,plain,(
% 0.19/0.55    spl7_2),
% 0.19/0.55    inference(avatar_split_clause,[],[f39,f70])).
% 0.19/0.55  fof(f39,plain,(
% 0.19/0.55    r2_hidden(sK1,sK3)),
% 0.19/0.55    inference(cnf_transformation,[],[f27])).
% 0.19/0.55  fof(f68,plain,(
% 0.19/0.55    ~spl7_1),
% 0.19/0.55    inference(avatar_split_clause,[],[f40,f66])).
% 0.19/0.55  fof(f40,plain,(
% 0.19/0.55    ~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))),
% 0.19/0.55    inference(cnf_transformation,[],[f27])).
% 0.19/0.55  % SZS output end Proof for theBenchmark
% 0.19/0.55  % (13488)------------------------------
% 0.19/0.55  % (13488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (13488)Termination reason: Refutation
% 0.19/0.55  
% 0.19/0.55  % (13488)Memory used [KB]: 10874
% 0.19/0.55  % (13488)Time elapsed: 0.151 s
% 0.19/0.55  % (13488)------------------------------
% 0.19/0.55  % (13488)------------------------------
% 0.19/0.55  % (13486)Refutation not found, incomplete strategy% (13486)------------------------------
% 0.19/0.55  % (13486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (13486)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (13486)Memory used [KB]: 10746
% 0.19/0.55  % (13486)Time elapsed: 0.157 s
% 0.19/0.55  % (13486)------------------------------
% 0.19/0.55  % (13486)------------------------------
% 0.19/0.55  % (13490)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.68/0.57  % (13463)Success in time 0.219 s
%------------------------------------------------------------------------------
