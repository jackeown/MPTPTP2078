%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:52 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 157 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  420 ( 810 expanded)
%              Number of equality atoms :   50 (  62 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f99,f155,f207,f210])).

fof(f210,plain,(
    spl7_19 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl7_19 ),
    inference(resolution,[],[f203,f87])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f41,f40])).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f203,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl7_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f207,plain,
    ( ~ spl7_19
    | ~ spl7_5
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_7
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f196,f153,f97,f76,f72,f68,f80,f202])).

fof(f80,plain,
    ( spl7_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f68,plain,
    ( spl7_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f72,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f76,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f97,plain,
    ( spl7_7
  <=> r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f153,plain,
    ( spl7_12
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f196,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(sK1,sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | spl7_7
    | ~ spl7_12 ),
    inference(resolution,[],[f194,f98])).

fof(f98,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f194,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) )
    | ~ spl7_12 ),
    inference(resolution,[],[f159,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f53,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f159,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1))
        | r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_12 ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1))
        | r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_12 ),
    inference(superposition,[],[f154,f57])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( ~ spl7_6
    | spl7_12
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f150,f84,f153,f84])).

fof(f84,plain,
    ( spl7_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f150,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,
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
    inference(superposition,[],[f146,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X2),k1_tops_2(sK0,X2,X1)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f91,f85])).

fof(f85,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f91,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f59,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2))
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
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
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f30,plain,(
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

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3)
          & r2_hidden(X6,X2)
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1)
        & r2_hidden(sK5(X0,X1,X2,X3),X2)
        & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( k9_subset_1(u1_struct_0(X0),X9,X1) = X7
          & r2_hidden(X9,X2)
          & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7
        & r2_hidden(sK6(X0,X1,X2,X7),X2)
        & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f99,plain,
    ( ~ spl7_4
    | ~ spl7_7
    | spl7_1 ),
    inference(avatar_split_clause,[],[f92,f64,f97,f76])).

fof(f64,plain,
    ( spl7_1
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f92,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1 ),
    inference(superposition,[],[f65,f57])).

fof(f65,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f86,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f34,f84])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))
    & r2_hidden(sK1,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f25,f24,f23,f22])).

fof(f22,plain,
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

fof(f23,plain,
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

fof(f24,plain,
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

fof(f25,plain,
    ( ? [X3] :
        ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3))
        & r2_hidden(sK1,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))
      & r2_hidden(sK1,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f82,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f35,f80])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f36,f76])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f38,plain,(
    r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f39,f64])).

fof(f39,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:46:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (29030)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (29046)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (29039)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (29032)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (29038)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.30/0.54  % (29028)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.55  % (29040)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.30/0.55  % (29024)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.44/0.55  % (29025)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.44/0.55  % (29029)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.44/0.55  % (29036)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.55  % (29047)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.44/0.56  % (29027)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.44/0.56  % (29037)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.56  % (29047)Refutation not found, incomplete strategy% (29047)------------------------------
% 1.44/0.56  % (29047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (29047)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (29047)Memory used [KB]: 10746
% 1.44/0.56  % (29047)Time elapsed: 0.131 s
% 1.44/0.56  % (29047)------------------------------
% 1.44/0.56  % (29047)------------------------------
% 1.44/0.56  % (29033)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.56  % (29035)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.56  % (29044)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.57  % (29048)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.44/0.57  % (29031)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.44/0.57  % (29050)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.57  % (29034)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.44/0.57  % (29045)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.57  % (29041)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.57  % (29043)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.57  % (29052)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.58  % (29049)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.58  % (29054)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.58  % (29042)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.44/0.59  % (29042)Refutation not found, incomplete strategy% (29042)------------------------------
% 1.44/0.59  % (29042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.59  % (29042)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.59  
% 1.44/0.59  % (29042)Memory used [KB]: 10746
% 1.44/0.59  % (29042)Time elapsed: 0.177 s
% 1.44/0.59  % (29042)------------------------------
% 1.44/0.59  % (29042)------------------------------
% 1.44/0.59  % (29051)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.59  % (29044)Refutation found. Thanks to Tanya!
% 1.44/0.59  % SZS status Theorem for theBenchmark
% 1.44/0.59  % SZS output start Proof for theBenchmark
% 1.44/0.59  fof(f211,plain,(
% 1.44/0.59    $false),
% 1.44/0.59    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f99,f155,f207,f210])).
% 1.44/0.59  fof(f210,plain,(
% 1.44/0.59    spl7_19),
% 1.44/0.59    inference(avatar_contradiction_clause,[],[f208])).
% 1.44/0.59  fof(f208,plain,(
% 1.44/0.59    $false | spl7_19),
% 1.44/0.59    inference(resolution,[],[f203,f87])).
% 1.44/0.59  fof(f87,plain,(
% 1.44/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.44/0.59    inference(forward_demodulation,[],[f41,f40])).
% 1.44/0.59  fof(f40,plain,(
% 1.44/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.44/0.59    inference(cnf_transformation,[],[f1])).
% 1.44/0.59  fof(f1,axiom,(
% 1.44/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.44/0.59  fof(f41,plain,(
% 1.44/0.59    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.44/0.59    inference(cnf_transformation,[],[f2])).
% 1.44/0.59  fof(f2,axiom,(
% 1.44/0.59    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.44/0.59  fof(f203,plain,(
% 1.44/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | spl7_19),
% 1.44/0.59    inference(avatar_component_clause,[],[f202])).
% 1.44/0.59  fof(f202,plain,(
% 1.44/0.59    spl7_19 <=> m1_subset_1(sK2,k1_zfmisc_1(sK2))),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.44/0.59  fof(f207,plain,(
% 1.44/0.59    ~spl7_19 | ~spl7_5 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_7 | ~spl7_12),
% 1.44/0.59    inference(avatar_split_clause,[],[f196,f153,f97,f76,f72,f68,f80,f202])).
% 1.44/0.59  fof(f80,plain,(
% 1.44/0.59    spl7_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.44/0.59  fof(f68,plain,(
% 1.44/0.59    spl7_2 <=> r2_hidden(sK1,sK3)),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.44/0.59  fof(f72,plain,(
% 1.44/0.59    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.44/0.59  fof(f76,plain,(
% 1.44/0.59    spl7_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.44/0.59  fof(f97,plain,(
% 1.44/0.59    spl7_7 <=> r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3))),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.44/0.59  fof(f153,plain,(
% 1.44/0.59    spl7_12 <=> ! [X1,X0,X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0)) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.44/0.59  fof(f196,plain,(
% 1.44/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | (spl7_7 | ~spl7_12)),
% 1.44/0.59    inference(resolution,[],[f194,f98])).
% 1.44/0.59  fof(f98,plain,(
% 1.44/0.59    ~r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3)) | spl7_7),
% 1.44/0.59    inference(avatar_component_clause,[],[f97])).
% 1.44/0.59  fof(f194,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) ) | ~spl7_12),
% 1.44/0.59    inference(resolution,[],[f159,f94])).
% 1.44/0.59  fof(f94,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.59    inference(duplicate_literal_removal,[],[f93])).
% 1.44/0.59  fof(f93,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.59    inference(superposition,[],[f53,f57])).
% 1.44/0.59  fof(f57,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.59    inference(definition_unfolding,[],[f54,f52])).
% 1.44/0.59  fof(f52,plain,(
% 1.44/0.59    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f5])).
% 1.44/0.59  fof(f5,axiom,(
% 1.44/0.59    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.44/0.59  fof(f54,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.59    inference(cnf_transformation,[],[f17])).
% 1.44/0.59  fof(f17,plain,(
% 1.44/0.59    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.44/0.59    inference(ennf_transformation,[],[f4])).
% 1.44/0.59  fof(f4,axiom,(
% 1.44/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.44/0.59  fof(f53,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.59    inference(cnf_transformation,[],[f16])).
% 1.44/0.59  fof(f16,plain,(
% 1.44/0.59    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.44/0.59    inference(ennf_transformation,[],[f3])).
% 1.44/0.59  fof(f3,axiom,(
% 1.44/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.44/0.59  fof(f159,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) | r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_12),
% 1.44/0.59    inference(duplicate_literal_removal,[],[f158])).
% 1.44/0.59  fof(f158,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) | r2_hidden(k1_setfam_1(k2_tarski(X0,X1)),k1_tops_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_12),
% 1.44/0.59    inference(superposition,[],[f154,f57])).
% 1.44/0.59  fof(f154,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0)) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_12),
% 1.44/0.59    inference(avatar_component_clause,[],[f153])).
% 1.44/0.59  fof(f155,plain,(
% 1.44/0.59    ~spl7_6 | spl7_12 | ~spl7_6),
% 1.44/0.59    inference(avatar_split_clause,[],[f150,f84,f153,f84])).
% 1.44/0.59  fof(f84,plain,(
% 1.44/0.59    spl7_6 <=> l1_pre_topc(sK0)),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.44/0.59  fof(f150,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2)) | ~l1_pre_topc(sK0)) ) | ~spl7_6),
% 1.44/0.59    inference(duplicate_literal_removal,[],[f149])).
% 1.44/0.59  fof(f149,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),k1_tops_2(sK0,X0,X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl7_6),
% 1.44/0.59    inference(superposition,[],[f146,f42])).
% 1.44/0.59  fof(f42,plain,(
% 1.44/0.59    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f14])).
% 1.44/0.59  fof(f14,plain,(
% 1.44/0.59    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.59    inference(ennf_transformation,[],[f7])).
% 1.44/0.59  fof(f7,axiom,(
% 1.44/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.44/0.59  fof(f146,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,X2),k1_tops_2(sK0,X2,X1))) ) | ~spl7_6),
% 1.44/0.59    inference(resolution,[],[f91,f85])).
% 1.44/0.59  fof(f85,plain,(
% 1.44/0.59    l1_pre_topc(sK0) | ~spl7_6),
% 1.44/0.59    inference(avatar_component_clause,[],[f84])).
% 1.44/0.59  fof(f91,plain,(
% 1.44/0.59    ( ! [X2,X0,X8,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2))) )),
% 1.44/0.59    inference(subsumption_resolution,[],[f59,f55])).
% 1.44/0.59  fof(f55,plain,(
% 1.44/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f19])).
% 1.44/0.59  fof(f19,plain,(
% 1.44/0.59    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.44/0.59    inference(flattening,[],[f18])).
% 1.44/0.59  fof(f18,plain,(
% 1.44/0.59    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.44/0.59    inference(ennf_transformation,[],[f9])).
% 1.44/0.59  fof(f9,axiom,(
% 1.44/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).
% 1.44/0.59  fof(f59,plain,(
% 1.44/0.59    ( ! [X2,X0,X8,X1] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),k1_tops_2(X0,X1,X2)) | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | ~m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.59    inference(equality_resolution,[],[f58])).
% 1.44/0.59  fof(f58,plain,(
% 1.44/0.59    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X8,X1),X3) | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X0),X8,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | k1_tops_2(X0,X1,X2) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.59    inference(equality_resolution,[],[f46])).
% 1.44/0.59  fof(f46,plain,(
% 1.44/0.59    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) | k1_tops_2(X0,X1,X2) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.59    inference(cnf_transformation,[],[f33])).
% 1.44/0.59  fof(f33,plain,(
% 1.44/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & ((sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1) & r2_hidden(sK5(X0,X1,X2,X3),X2) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1,X2,X3),X3)) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X7] : (((r2_hidden(X7,X3) | ! [X8] : (k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7 & r2_hidden(sK6(X0,X1,X2,X7),X2) & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X7,X3))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 1.44/0.59  fof(f30,plain,(
% 1.44/0.59    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = X4 & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) => ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != sK4(X0,X1,X2,X3) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3) & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1,X2,X3),X3)) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 1.44/0.59    introduced(choice_axiom,[])).
% 1.44/0.59  fof(f31,plain,(
% 1.44/0.59    ! [X3,X2,X1,X0] : (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = sK4(X0,X1,X2,X3) & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) => (sK4(X0,X1,X2,X3) = k9_subset_1(u1_struct_0(X0),sK5(X0,X1,X2,X3),X1) & r2_hidden(sK5(X0,X1,X2,X3),X2) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.59    introduced(choice_axiom,[])).
% 1.44/0.59  fof(f32,plain,(
% 1.44/0.59    ! [X7,X2,X1,X0] : (? [X9] : (k9_subset_1(u1_struct_0(X0),X9,X1) = X7 & r2_hidden(X9,X2) & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X7),X1) = X7 & r2_hidden(sK6(X0,X1,X2,X7),X2) & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.59    introduced(choice_axiom,[])).
% 1.44/0.59  fof(f29,plain,(
% 1.44/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X6] : (k9_subset_1(u1_struct_0(X0),X6,X1) = X4 & r2_hidden(X6,X2) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X7] : (((r2_hidden(X7,X3) | ! [X8] : (k9_subset_1(u1_struct_0(X0),X8,X1) != X7 | ~r2_hidden(X8,X2) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X9] : (k9_subset_1(u1_struct_0(X0),X9,X1) = X7 & r2_hidden(X9,X2) & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X7,X3))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.59    inference(rectify,[],[f28])).
% 1.44/0.59  fof(f28,plain,(
% 1.44/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X4] : (((r2_hidden(X4,X3) | ! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.59    inference(flattening,[],[f27])).
% 1.44/0.59  fof(f27,plain,(
% 1.44/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tops_2(X0,X1,X2) = X3 | ? [X4] : (((! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3)) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) & (! [X4] : (((r2_hidden(X4,X3) | ! [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | k1_tops_2(X0,X1,X2) != X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.59    inference(nnf_transformation,[],[f15])).
% 1.44/0.59  fof(f15,plain,(
% 1.44/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : ((r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.59    inference(ennf_transformation,[],[f8])).
% 1.44/0.59  fof(f8,axiom,(
% 1.44/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) => (k1_tops_2(X0,X1,X2) = X3 <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) => (r2_hidden(X4,X3) <=> ? [X5] : (k9_subset_1(u1_struct_0(X0),X5,X1) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))))))))))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_2)).
% 1.44/0.59  fof(f99,plain,(
% 1.44/0.59    ~spl7_4 | ~spl7_7 | spl7_1),
% 1.44/0.59    inference(avatar_split_clause,[],[f92,f64,f97,f76])).
% 1.44/0.59  fof(f64,plain,(
% 1.44/0.59    spl7_1 <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))),
% 1.44/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.44/0.59  fof(f92,plain,(
% 1.44/0.59    ~r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k1_tops_2(sK0,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_1),
% 1.44/0.59    inference(superposition,[],[f65,f57])).
% 1.44/0.59  fof(f65,plain,(
% 1.44/0.59    ~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) | spl7_1),
% 1.44/0.59    inference(avatar_component_clause,[],[f64])).
% 1.44/0.59  fof(f86,plain,(
% 1.44/0.59    spl7_6),
% 1.44/0.59    inference(avatar_split_clause,[],[f34,f84])).
% 1.44/0.59  fof(f34,plain,(
% 1.44/0.59    l1_pre_topc(sK0)),
% 1.44/0.59    inference(cnf_transformation,[],[f26])).
% 1.44/0.59  fof(f26,plain,(
% 1.44/0.59    (((~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) & r2_hidden(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.44/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f25,f24,f23,f22])).
% 1.44/0.59  fof(f22,plain,(
% 1.44/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.44/0.59    introduced(choice_axiom,[])).
% 1.44/0.59  fof(f23,plain,(
% 1.44/0.59    ? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.44/0.59    introduced(choice_axiom,[])).
% 1.44/0.59  fof(f24,plain,(
% 1.44/0.59    ? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_tops_2(sK0,X2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.44/0.59    introduced(choice_axiom,[])).
% 1.44/0.59  fof(f25,plain,(
% 1.44/0.59    ? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,X3)) & r2_hidden(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3)) & r2_hidden(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.44/0.59    introduced(choice_axiom,[])).
% 1.44/0.59  fof(f13,plain,(
% 1.44/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.44/0.59    inference(flattening,[],[f12])).
% 1.44/0.59  fof(f12,plain,(
% 1.44/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) & r2_hidden(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.44/0.59    inference(ennf_transformation,[],[f11])).
% 1.44/0.59  fof(f11,negated_conjecture,(
% 1.44/0.59    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 1.44/0.59    inference(negated_conjecture,[],[f10])).
% 1.44/0.59  fof(f10,conjecture,(
% 1.44/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,X3) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)))))))),
% 1.44/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_2)).
% 1.44/0.59  fof(f82,plain,(
% 1.44/0.59    spl7_5),
% 1.44/0.59    inference(avatar_split_clause,[],[f35,f80])).
% 1.44/0.59  fof(f35,plain,(
% 1.44/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.44/0.59    inference(cnf_transformation,[],[f26])).
% 1.44/0.59  fof(f78,plain,(
% 1.44/0.59    spl7_4),
% 1.44/0.59    inference(avatar_split_clause,[],[f36,f76])).
% 1.44/0.59  fof(f36,plain,(
% 1.44/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.44/0.59    inference(cnf_transformation,[],[f26])).
% 1.44/0.59  fof(f74,plain,(
% 1.44/0.59    spl7_3),
% 1.44/0.59    inference(avatar_split_clause,[],[f37,f72])).
% 1.44/0.59  fof(f37,plain,(
% 1.44/0.59    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.44/0.59    inference(cnf_transformation,[],[f26])).
% 1.44/0.59  fof(f70,plain,(
% 1.44/0.59    spl7_2),
% 1.44/0.59    inference(avatar_split_clause,[],[f38,f68])).
% 1.44/0.59  fof(f38,plain,(
% 1.44/0.59    r2_hidden(sK1,sK3)),
% 1.44/0.59    inference(cnf_transformation,[],[f26])).
% 1.44/0.59  fof(f66,plain,(
% 1.44/0.59    ~spl7_1),
% 1.44/0.59    inference(avatar_split_clause,[],[f39,f64])).
% 1.44/0.59  fof(f39,plain,(
% 1.44/0.59    ~r2_hidden(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_2(sK0,sK2,sK3))),
% 1.44/0.59    inference(cnf_transformation,[],[f26])).
% 1.44/0.59  % SZS output end Proof for theBenchmark
% 1.44/0.59  % (29044)------------------------------
% 1.44/0.59  % (29044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.59  % (29044)Termination reason: Refutation
% 1.44/0.59  
% 1.44/0.59  % (29044)Memory used [KB]: 11001
% 1.44/0.59  % (29044)Time elapsed: 0.170 s
% 1.44/0.59  % (29044)------------------------------
% 1.44/0.59  % (29044)------------------------------
% 1.44/0.60  % (29023)Success in time 0.231 s
%------------------------------------------------------------------------------
