%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:04 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 261 expanded)
%              Number of leaves         :   27 (  92 expanded)
%              Depth                    :    7
%              Number of atoms          :  279 ( 653 expanded)
%              Number of equality atoms :   11 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f729,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f98,f192,f218,f249,f266,f273,f361,f442,f534,f580,f596,f647,f694,f706,f728])).

fof(f728,plain,(
    spl3_77 ),
    inference(avatar_contradiction_clause,[],[f715])).

fof(f715,plain,
    ( $false
    | spl3_77 ),
    inference(unit_resulting_resolution,[],[f45,f43,f705,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f705,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2)))
    | spl3_77 ),
    inference(avatar_component_clause,[],[f703])).

fof(f703,plain,
    ( spl3_77
  <=> r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f40,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f706,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | ~ spl3_77
    | spl3_75 ),
    inference(avatar_split_clause,[],[f701,f691,f703,f198,f194])).

fof(f194,plain,
    ( spl3_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f198,plain,
    ( spl3_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f691,plain,
    ( spl3_75
  <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f701,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_75 ),
    inference(superposition,[],[f693,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f39,f31])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f693,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_75 ),
    inference(avatar_component_clause,[],[f691])).

fof(f694,plain,
    ( ~ spl3_6
    | ~ spl3_75
    | ~ spl3_46
    | ~ spl3_16
    | spl3_35 ),
    inference(avatar_split_clause,[],[f688,f358,f198,f434,f691,f88])).

fof(f88,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f434,plain,
    ( spl3_46
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f358,plain,
    ( spl3_35
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f688,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | spl3_35 ),
    inference(resolution,[],[f360,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
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
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f360,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f358])).

fof(f647,plain,
    ( spl3_47
    | ~ spl3_54 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | spl3_47
    | ~ spl3_54 ),
    inference(unit_resulting_resolution,[],[f26,f25,f40,f43,f522,f441,f252])).

fof(f252,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r1_tarski(X2,X4)
      | ~ l1_pre_topc(X3)
      | ~ r1_tarski(X5,k1_tops_1(X3,X2))
      | r1_tarski(X5,k1_tops_1(X3,X4)) ) ),
    inference(resolution,[],[f28,f37])).

fof(f441,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl3_47
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f522,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f521])).

fof(f521,plain,
    ( spl3_54
  <=> m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f596,plain,
    ( spl3_54
    | ~ spl3_55 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | spl3_54
    | ~ spl3_55 ),
    inference(unit_resulting_resolution,[],[f532,f523,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f523,plain,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_54 ),
    inference(avatar_component_clause,[],[f521])).

fof(f532,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f531])).

fof(f531,plain,
    ( spl3_55
  <=> r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f580,plain,(
    spl3_55 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | spl3_55 ),
    inference(unit_resulting_resolution,[],[f50,f49,f533,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f31])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f533,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | spl3_55 ),
    inference(avatar_component_clause,[],[f531])).

fof(f49,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f36,f23])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f36,f25])).

fof(f534,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | ~ spl3_55
    | spl3_46 ),
    inference(avatar_split_clause,[],[f529,f434,f531,f198,f194])).

fof(f529,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_46 ),
    inference(superposition,[],[f518,f42])).

fof(f518,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
    | spl3_46 ),
    inference(resolution,[],[f436,f35])).

fof(f436,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f434])).

fof(f442,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | ~ spl3_47
    | spl3_34 ),
    inference(avatar_split_clause,[],[f428,f354,f439,f198,f194])).

fof(f354,plain,
    ( spl3_34
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f428,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_34 ),
    inference(superposition,[],[f356,f42])).

fof(f356,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f354])).

fof(f361,plain,
    ( ~ spl3_34
    | ~ spl3_35
    | spl3_14 ),
    inference(avatar_split_clause,[],[f351,f189,f358,f354])).

fof(f189,plain,
    ( spl3_14
  <=> r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f351,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_14 ),
    inference(resolution,[],[f191,f41])).

fof(f191,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f189])).

fof(f273,plain,(
    spl3_16 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl3_16 ),
    inference(subsumption_resolution,[],[f23,f200])).

fof(f200,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f198])).

fof(f266,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl3_15 ),
    inference(subsumption_resolution,[],[f25,f196])).

fof(f196,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f194])).

fof(f249,plain,
    ( ~ spl3_5
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl3_5
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f49,f86,f237,f37])).

fof(f237,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_13 ),
    inference(resolution,[],[f187,f35])).

fof(f187,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl3_13
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f86,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_5
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f218,plain,
    ( ~ spl3_7
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl3_7
    | spl3_12 ),
    inference(unit_resulting_resolution,[],[f50,f95,f206,f37])).

fof(f206,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_12 ),
    inference(resolution,[],[f183,f35])).

fof(f183,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl3_12
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f95,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_7
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f192,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f178,f189,f185,f181])).

fof(f178,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f24,f42])).

fof(f24,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f98,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f26,f90])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f96,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f81,f88,f93])).

fof(f81,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f27,f25])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f91,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f80,f88,f84])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f27,f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n013.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:18:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (1228)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (1227)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (1246)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (1238)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (1230)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (1234)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (1229)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (1225)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (1242)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (1226)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (1250)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (1224)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (1252)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (1235)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (1251)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (1247)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (1241)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (1248)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (1244)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (1243)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (1237)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (1240)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (1233)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (1245)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (1223)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.56  % (1236)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (1249)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.56  % (1232)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.33/0.57  % (1239)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.66/0.58  % (1231)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.66/0.61  % (1236)Refutation found. Thanks to Tanya!
% 1.66/0.61  % SZS status Theorem for theBenchmark
% 1.66/0.61  % SZS output start Proof for theBenchmark
% 1.66/0.61  fof(f729,plain,(
% 1.66/0.61    $false),
% 1.66/0.61    inference(avatar_sat_refutation,[],[f91,f96,f98,f192,f218,f249,f266,f273,f361,f442,f534,f580,f596,f647,f694,f706,f728])).
% 1.66/0.61  fof(f728,plain,(
% 1.66/0.61    spl3_77),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f715])).
% 1.66/0.61  fof(f715,plain,(
% 1.66/0.61    $false | spl3_77),
% 1.66/0.61    inference(unit_resulting_resolution,[],[f45,f43,f705,f37])).
% 1.66/0.61  fof(f37,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f18])).
% 1.66/0.61  fof(f18,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.66/0.61    inference(flattening,[],[f17])).
% 1.66/0.61  fof(f17,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.66/0.61    inference(ennf_transformation,[],[f2])).
% 1.66/0.61  fof(f2,axiom,(
% 1.66/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.66/0.61  fof(f705,plain,(
% 1.66/0.61    ~r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) | spl3_77),
% 1.66/0.61    inference(avatar_component_clause,[],[f703])).
% 1.66/0.61  fof(f703,plain,(
% 1.66/0.61    spl3_77 <=> r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 1.66/0.61  fof(f43,plain,(
% 1.66/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.61    inference(equality_resolution,[],[f33])).
% 1.66/0.61  fof(f33,plain,(
% 1.66/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.66/0.61    inference(cnf_transformation,[],[f1])).
% 1.66/0.61  fof(f1,axiom,(
% 1.66/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.61  fof(f45,plain,(
% 1.66/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 1.66/0.61    inference(superposition,[],[f40,f30])).
% 1.66/0.61  fof(f30,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f5])).
% 1.66/0.61  fof(f5,axiom,(
% 1.66/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.66/0.61  fof(f40,plain,(
% 1.66/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 1.66/0.61    inference(definition_unfolding,[],[f29,f31])).
% 1.66/0.61  fof(f31,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f6])).
% 1.66/0.61  fof(f6,axiom,(
% 1.66/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.66/0.61  fof(f29,plain,(
% 1.66/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f3])).
% 1.66/0.61  fof(f3,axiom,(
% 1.66/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.66/0.61  fof(f706,plain,(
% 1.66/0.61    ~spl3_15 | ~spl3_16 | ~spl3_77 | spl3_75),
% 1.66/0.61    inference(avatar_split_clause,[],[f701,f691,f703,f198,f194])).
% 1.66/0.61  fof(f194,plain,(
% 1.66/0.61    spl3_15 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.66/0.61  fof(f198,plain,(
% 1.66/0.61    spl3_16 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.66/0.61  fof(f691,plain,(
% 1.66/0.61    spl3_75 <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 1.66/0.61  fof(f701,plain,(
% 1.66/0.61    ~r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_75),
% 1.66/0.61    inference(superposition,[],[f693,f42])).
% 1.66/0.61  fof(f42,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.66/0.61    inference(definition_unfolding,[],[f39,f31])).
% 1.66/0.61  fof(f39,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f22])).
% 1.66/0.61  fof(f22,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.61    inference(flattening,[],[f21])).
% 1.66/0.61  fof(f21,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.66/0.61    inference(ennf_transformation,[],[f7])).
% 1.66/0.61  fof(f7,axiom,(
% 1.66/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.66/0.61  fof(f693,plain,(
% 1.66/0.61    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl3_75),
% 1.66/0.61    inference(avatar_component_clause,[],[f691])).
% 1.66/0.61  fof(f694,plain,(
% 1.66/0.61    ~spl3_6 | ~spl3_75 | ~spl3_46 | ~spl3_16 | spl3_35),
% 1.66/0.61    inference(avatar_split_clause,[],[f688,f358,f198,f434,f691,f88])).
% 1.66/0.61  fof(f88,plain,(
% 1.66/0.61    spl3_6 <=> l1_pre_topc(sK0)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.66/0.61  fof(f434,plain,(
% 1.66/0.61    spl3_46 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.66/0.61  fof(f358,plain,(
% 1.66/0.61    spl3_35 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 1.66/0.61  fof(f688,plain,(
% 1.66/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~l1_pre_topc(sK0) | spl3_35),
% 1.66/0.61    inference(resolution,[],[f360,f28])).
% 1.66/0.61  fof(f28,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f16])).
% 1.66/0.61  fof(f16,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/0.61    inference(flattening,[],[f15])).
% 1.66/0.61  fof(f15,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/0.61    inference(ennf_transformation,[],[f10])).
% 1.66/0.61  fof(f10,axiom,(
% 1.66/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.66/0.61  fof(f360,plain,(
% 1.66/0.61    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_35),
% 1.66/0.61    inference(avatar_component_clause,[],[f358])).
% 1.66/0.61  fof(f647,plain,(
% 1.66/0.61    spl3_47 | ~spl3_54),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f644])).
% 1.66/0.61  fof(f644,plain,(
% 1.66/0.61    $false | (spl3_47 | ~spl3_54)),
% 1.66/0.61    inference(unit_resulting_resolution,[],[f26,f25,f40,f43,f522,f441,f252])).
% 1.66/0.61  fof(f252,plain,(
% 1.66/0.61    ( ! [X4,X2,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~r1_tarski(X2,X4) | ~l1_pre_topc(X3) | ~r1_tarski(X5,k1_tops_1(X3,X2)) | r1_tarski(X5,k1_tops_1(X3,X4))) )),
% 1.66/0.61    inference(resolution,[],[f28,f37])).
% 1.66/0.61  fof(f441,plain,(
% 1.66/0.61    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) | spl3_47),
% 1.66/0.61    inference(avatar_component_clause,[],[f439])).
% 1.66/0.61  fof(f439,plain,(
% 1.66/0.61    spl3_47 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 1.66/0.61  fof(f522,plain,(
% 1.66/0.61    m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_54),
% 1.66/0.61    inference(avatar_component_clause,[],[f521])).
% 1.66/0.61  fof(f521,plain,(
% 1.66/0.61    spl3_54 <=> m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 1.66/0.61  fof(f25,plain,(
% 1.66/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.61    inference(cnf_transformation,[],[f13])).
% 1.66/0.61  fof(f13,plain,(
% 1.66/0.61    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.66/0.61    inference(ennf_transformation,[],[f12])).
% 1.66/0.61  fof(f12,negated_conjecture,(
% 1.66/0.61    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.66/0.61    inference(negated_conjecture,[],[f11])).
% 1.66/0.61  fof(f11,conjecture,(
% 1.66/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).
% 1.66/0.61  fof(f26,plain,(
% 1.66/0.61    l1_pre_topc(sK0)),
% 1.66/0.61    inference(cnf_transformation,[],[f13])).
% 1.66/0.61  fof(f596,plain,(
% 1.66/0.61    spl3_54 | ~spl3_55),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f594])).
% 1.66/0.61  fof(f594,plain,(
% 1.66/0.61    $false | (spl3_54 | ~spl3_55)),
% 1.66/0.61    inference(unit_resulting_resolution,[],[f532,f523,f35])).
% 1.66/0.61  fof(f35,plain,(
% 1.66/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f8])).
% 1.66/0.61  fof(f8,axiom,(
% 1.66/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.66/0.61  fof(f523,plain,(
% 1.66/0.61    ~m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_54),
% 1.66/0.61    inference(avatar_component_clause,[],[f521])).
% 1.66/0.61  fof(f532,plain,(
% 1.66/0.61    r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) | ~spl3_55),
% 1.66/0.61    inference(avatar_component_clause,[],[f531])).
% 1.66/0.61  fof(f531,plain,(
% 1.66/0.61    spl3_55 <=> r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 1.66/0.61  fof(f580,plain,(
% 1.66/0.61    spl3_55),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f573])).
% 1.66/0.61  fof(f573,plain,(
% 1.66/0.61    $false | spl3_55),
% 1.66/0.61    inference(unit_resulting_resolution,[],[f50,f49,f533,f41])).
% 1.66/0.61  fof(f41,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.66/0.61    inference(definition_unfolding,[],[f38,f31])).
% 1.66/0.61  fof(f38,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f20])).
% 1.66/0.61  fof(f20,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.66/0.61    inference(flattening,[],[f19])).
% 1.66/0.61  fof(f19,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.66/0.61    inference(ennf_transformation,[],[f4])).
% 1.66/0.61  fof(f4,axiom,(
% 1.66/0.61    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.66/0.61  fof(f533,plain,(
% 1.66/0.61    ~r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) | spl3_55),
% 1.66/0.61    inference(avatar_component_clause,[],[f531])).
% 1.66/0.61  fof(f49,plain,(
% 1.66/0.61    r1_tarski(sK2,u1_struct_0(sK0))),
% 1.66/0.61    inference(resolution,[],[f36,f23])).
% 1.66/0.61  fof(f23,plain,(
% 1.66/0.61    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.61    inference(cnf_transformation,[],[f13])).
% 1.66/0.61  fof(f36,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f8])).
% 1.66/0.61  fof(f50,plain,(
% 1.66/0.61    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.66/0.61    inference(resolution,[],[f36,f25])).
% 1.66/0.61  fof(f534,plain,(
% 1.66/0.61    ~spl3_15 | ~spl3_16 | ~spl3_55 | spl3_46),
% 1.66/0.61    inference(avatar_split_clause,[],[f529,f434,f531,f198,f194])).
% 1.66/0.61  fof(f529,plain,(
% 1.66/0.61    ~r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_46),
% 1.66/0.61    inference(superposition,[],[f518,f42])).
% 1.66/0.61  fof(f518,plain,(
% 1.66/0.61    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) | spl3_46),
% 1.66/0.61    inference(resolution,[],[f436,f35])).
% 1.66/0.61  fof(f436,plain,(
% 1.66/0.61    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_46),
% 1.66/0.61    inference(avatar_component_clause,[],[f434])).
% 1.66/0.61  fof(f442,plain,(
% 1.66/0.61    ~spl3_15 | ~spl3_16 | ~spl3_47 | spl3_34),
% 1.66/0.61    inference(avatar_split_clause,[],[f428,f354,f439,f198,f194])).
% 1.66/0.61  fof(f354,plain,(
% 1.66/0.61    spl3_34 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.66/0.61  fof(f428,plain,(
% 1.66/0.61    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_34),
% 1.66/0.61    inference(superposition,[],[f356,f42])).
% 1.66/0.61  fof(f356,plain,(
% 1.66/0.61    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_34),
% 1.66/0.61    inference(avatar_component_clause,[],[f354])).
% 1.66/0.61  fof(f361,plain,(
% 1.66/0.61    ~spl3_34 | ~spl3_35 | spl3_14),
% 1.66/0.61    inference(avatar_split_clause,[],[f351,f189,f358,f354])).
% 1.66/0.61  fof(f189,plain,(
% 1.66/0.61    spl3_14 <=> r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.66/0.61  fof(f351,plain,(
% 1.66/0.61    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_14),
% 1.66/0.61    inference(resolution,[],[f191,f41])).
% 1.66/0.61  fof(f191,plain,(
% 1.66/0.61    ~r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_14),
% 1.66/0.61    inference(avatar_component_clause,[],[f189])).
% 1.66/0.61  fof(f273,plain,(
% 1.66/0.61    spl3_16),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f269])).
% 1.66/0.61  fof(f269,plain,(
% 1.66/0.61    $false | spl3_16),
% 1.66/0.61    inference(subsumption_resolution,[],[f23,f200])).
% 1.66/0.61  fof(f200,plain,(
% 1.66/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_16),
% 1.66/0.61    inference(avatar_component_clause,[],[f198])).
% 1.66/0.61  fof(f266,plain,(
% 1.66/0.61    spl3_15),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f262])).
% 1.66/0.61  fof(f262,plain,(
% 1.66/0.61    $false | spl3_15),
% 1.66/0.61    inference(subsumption_resolution,[],[f25,f196])).
% 1.66/0.61  fof(f196,plain,(
% 1.66/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 1.66/0.61    inference(avatar_component_clause,[],[f194])).
% 1.66/0.61  fof(f249,plain,(
% 1.66/0.61    ~spl3_5 | spl3_13),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f241])).
% 1.66/0.61  fof(f241,plain,(
% 1.66/0.61    $false | (~spl3_5 | spl3_13)),
% 1.66/0.61    inference(unit_resulting_resolution,[],[f49,f86,f237,f37])).
% 1.66/0.61  fof(f237,plain,(
% 1.66/0.61    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_13),
% 1.66/0.61    inference(resolution,[],[f187,f35])).
% 1.66/0.61  fof(f187,plain,(
% 1.66/0.61    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_13),
% 1.66/0.61    inference(avatar_component_clause,[],[f185])).
% 1.66/0.61  fof(f185,plain,(
% 1.66/0.61    spl3_13 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.66/0.61  fof(f86,plain,(
% 1.66/0.61    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl3_5),
% 1.66/0.61    inference(avatar_component_clause,[],[f84])).
% 1.66/0.61  fof(f84,plain,(
% 1.66/0.61    spl3_5 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.66/0.61  fof(f218,plain,(
% 1.66/0.61    ~spl3_7 | spl3_12),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f210])).
% 1.66/0.61  fof(f210,plain,(
% 1.66/0.61    $false | (~spl3_7 | spl3_12)),
% 1.66/0.61    inference(unit_resulting_resolution,[],[f50,f95,f206,f37])).
% 1.66/0.61  fof(f206,plain,(
% 1.66/0.61    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_12),
% 1.66/0.61    inference(resolution,[],[f183,f35])).
% 1.66/0.61  fof(f183,plain,(
% 1.66/0.61    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_12),
% 1.66/0.61    inference(avatar_component_clause,[],[f181])).
% 1.66/0.61  fof(f181,plain,(
% 1.66/0.61    spl3_12 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.66/0.61  fof(f95,plain,(
% 1.66/0.61    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_7),
% 1.66/0.61    inference(avatar_component_clause,[],[f93])).
% 1.66/0.61  fof(f93,plain,(
% 1.66/0.61    spl3_7 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.66/0.61  fof(f192,plain,(
% 1.66/0.61    ~spl3_12 | ~spl3_13 | ~spl3_14),
% 1.66/0.61    inference(avatar_split_clause,[],[f178,f189,f185,f181])).
% 1.66/0.61  fof(f178,plain,(
% 1.66/0.61    ~r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.61    inference(superposition,[],[f24,f42])).
% 1.66/0.61  fof(f24,plain,(
% 1.66/0.61    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.66/0.61    inference(cnf_transformation,[],[f13])).
% 1.66/0.61  fof(f98,plain,(
% 1.66/0.61    spl3_6),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f97])).
% 1.66/0.61  fof(f97,plain,(
% 1.66/0.61    $false | spl3_6),
% 1.66/0.61    inference(subsumption_resolution,[],[f26,f90])).
% 1.66/0.61  fof(f90,plain,(
% 1.66/0.61    ~l1_pre_topc(sK0) | spl3_6),
% 1.66/0.61    inference(avatar_component_clause,[],[f88])).
% 1.66/0.61  fof(f96,plain,(
% 1.66/0.61    spl3_7 | ~spl3_6),
% 1.66/0.61    inference(avatar_split_clause,[],[f81,f88,f93])).
% 1.66/0.61  fof(f81,plain,(
% 1.66/0.61    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.66/0.61    inference(resolution,[],[f27,f25])).
% 1.66/0.61  fof(f27,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f14])).
% 1.66/0.61  fof(f14,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/0.61    inference(ennf_transformation,[],[f9])).
% 1.66/0.61  fof(f9,axiom,(
% 1.66/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.66/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.66/0.61  fof(f91,plain,(
% 1.66/0.61    spl3_5 | ~spl3_6),
% 1.66/0.61    inference(avatar_split_clause,[],[f80,f88,f84])).
% 1.66/0.61  fof(f80,plain,(
% 1.66/0.61    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 1.66/0.61    inference(resolution,[],[f27,f23])).
% 1.66/0.61  % SZS output end Proof for theBenchmark
% 1.66/0.61  % (1236)------------------------------
% 1.66/0.61  % (1236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (1236)Termination reason: Refutation
% 1.66/0.61  
% 1.66/0.61  % (1236)Memory used [KB]: 6652
% 1.66/0.61  % (1236)Time elapsed: 0.212 s
% 1.66/0.61  % (1236)------------------------------
% 1.66/0.61  % (1236)------------------------------
% 1.66/0.61  % (1222)Success in time 0.252 s
%------------------------------------------------------------------------------
