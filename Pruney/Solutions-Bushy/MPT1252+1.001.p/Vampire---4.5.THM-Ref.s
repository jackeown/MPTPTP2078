%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1252+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:33 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 237 expanded)
%              Number of leaves         :   22 (  77 expanded)
%              Depth                    :   22
%              Number of atoms          :  326 ( 654 expanded)
%              Number of equality atoms :   16 (  66 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f988,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f64,f953,f957,f962,f967,f969,f982,f987])).

fof(f987,plain,
    ( ~ spl2_9
    | spl2_6 ),
    inference(avatar_split_clause,[],[f981,f950,f984])).

fof(f984,plain,
    ( spl2_9
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f950,plain,
    ( spl2_6
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f981,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl2_6 ),
    inference(resolution,[],[f952,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f952,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f950])).

fof(f982,plain,
    ( ~ spl2_2
    | spl2_6 ),
    inference(avatar_split_clause,[],[f980,f950,f50])).

fof(f50,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f980,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_6 ),
    inference(resolution,[],[f952,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f969,plain,
    ( spl2_8
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f968,f946,f964])).

fof(f964,plain,
    ( spl2_8
  <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f946,plain,
    ( spl2_5
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f968,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_5 ),
    inference(resolution,[],[f947,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f947,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f946])).

fof(f967,plain,
    ( ~ spl2_8
    | spl2_5 ),
    inference(avatar_split_clause,[],[f956,f946,f964])).

fof(f956,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl2_5 ),
    inference(resolution,[],[f948,f40])).

fof(f948,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f946])).

fof(f962,plain,
    ( ~ spl2_7
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5 ),
    inference(avatar_split_clause,[],[f955,f946,f55,f50,f959])).

fof(f959,plain,
    ( spl2_7
  <=> r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f55,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f955,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | spl2_5 ),
    inference(resolution,[],[f948,f226])).

fof(f226,plain,(
    ! [X4,X2,X3] :
      ( m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(X4))
      | ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r1_tarski(k2_pre_topc(X3,X2),X4) ) ),
    inference(resolution,[],[f223,f40])).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f169,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f169,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(k2_pre_topc(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))
      | ~ m1_subset_1(k2_pre_topc(X14,X15),k1_zfmisc_1(X16))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ l1_pre_topc(X14)
      | m1_subset_1(k2_tops_1(X14,X15),k1_zfmisc_1(X16)) ) ),
    inference(superposition,[],[f70,f126])).

fof(f126,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)),k2_pre_topc(X2,X3)) = k2_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f33,f84])).

fof(f84,plain,(
    ! [X6,X8,X7] :
      ( k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6)) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X6,X8,X7] :
      ( k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f43,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

fof(f70,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k3_xboole_0(X4,X5),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k3_xboole_0(X4,X5),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f41,f42])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f957,plain,
    ( ~ spl2_3
    | ~ spl2_2
    | spl2_5 ),
    inference(avatar_split_clause,[],[f954,f946,f50,f55])).

fof(f954,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_5 ),
    inference(resolution,[],[f948,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f953,plain,
    ( ~ spl2_5
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f944,f45,f50,f950,f55,f946])).

fof(f45,plain,
    ( spl2_1
  <=> r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f944,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_1 ),
    inference(resolution,[],[f789,f47])).

fof(f47,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f789,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f788])).

fof(f788,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f787,f179])).

fof(f179,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k2_pre_topc(X3,X2),X4)
      | ~ l1_pre_topc(X3)
      | r1_tarski(k2_tops_1(X3,X2),X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(resolution,[],[f176,f40])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k2_tops_1(X0,X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k2_tops_1(X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f170,f37])).

fof(f170,plain,(
    ! [X19,X17,X18] :
      ( ~ m1_subset_1(k2_pre_topc(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))
      | ~ m1_subset_1(k2_pre_topc(X17,X18),k1_zfmisc_1(X19))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | ~ l1_pre_topc(X17)
      | r1_tarski(k2_tops_1(X17,X18),X19) ) ),
    inference(superposition,[],[f71,f126])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f67,f42])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f41,f39])).

fof(f787,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_pre_topc(X2,k2_tops_1(X2,X3)),k2_tops_1(X2,X3))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X2),X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(global_subsumption,[],[f37,f783])).

fof(f783,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f778])).

fof(f778,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f709,f126])).

fof(f709,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k3_xboole_0(k2_pre_topc(X0,X2),k2_pre_topc(X0,X1))),k3_xboole_0(k2_pre_topc(X0,X2),k2_pre_topc(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(global_subsumption,[],[f37,f703])).

fof(f703,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k3_xboole_0(k2_pre_topc(X0,X2),k2_pre_topc(X0,X1))),k3_xboole_0(k2_pre_topc(X0,X2),k2_pre_topc(X0,X1)))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f696])).

fof(f696,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k3_xboole_0(k2_pre_topc(X0,X2),k2_pre_topc(X0,X1))),k3_xboole_0(k2_pre_topc(X0,X2),k2_pre_topc(X0,X1)))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f642,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f642,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k3_xboole_0(k2_pre_topc(X0,X1),X2)),k3_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(global_subsumption,[],[f37,f640])).

fof(f640,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k3_xboole_0(k2_pre_topc(X0,X1),X2)),k3_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f631])).

fof(f631,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k3_xboole_0(k2_pre_topc(X0,X1),X2)),k3_xboole_0(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f602,f38])).

fof(f602,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k2_pre_topc(X4,k3_xboole_0(X6,X5)),k3_xboole_0(k2_pre_topc(X4,X6),k2_pre_topc(X4,X5)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4) ) ),
    inference(duplicate_literal_removal,[],[f585])).

fof(f585,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k2_pre_topc(X4,k3_xboole_0(X6,X5)),k3_xboole_0(k2_pre_topc(X4,X6),k2_pre_topc(X4,X5)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(superposition,[],[f581,f84])).

fof(f581,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k2_pre_topc(X4,k9_subset_1(u1_struct_0(X4),X5,X6)),k3_xboole_0(k2_pre_topc(X4,X6),k2_pre_topc(X4,X5)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4) ) ),
    inference(global_subsumption,[],[f37,f193])).

fof(f193,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k2_pre_topc(X4,k9_subset_1(u1_struct_0(X4),X5,X6)),k3_xboole_0(k2_pre_topc(X4,X6),k2_pre_topc(X4,X5)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ m1_subset_1(k2_pre_topc(X4,X5),k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(superposition,[],[f34,f84])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f64,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f59,f50,f61])).

fof(f61,plain,
    ( spl2_4
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f59,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f39,f52])).

fof(f52,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f58,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tops_1)).

fof(f53,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f31,f50])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f32,f45])).

fof(f32,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
