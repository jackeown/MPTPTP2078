%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 199 expanded)
%              Number of leaves         :   24 (  82 expanded)
%              Depth                    :    8
%              Number of atoms          :  244 ( 536 expanded)
%              Number of equality atoms :    9 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f797,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f177,f197,f199,f227,f233,f352,f435,f728,f745,f777,f796])).

fof(f796,plain,(
    spl3_33 ),
    inference(avatar_contradiction_clause,[],[f794])).

fof(f794,plain,
    ( $false
    | spl3_33 ),
    inference(resolution,[],[f780,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
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
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f780,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_33 ),
    inference(resolution,[],[f743,f75])).

fof(f75,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k9_subset_1(X5,X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5)) ) ),
    inference(superposition,[],[f47,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f32,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f34,f34])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f743,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f741])).

fof(f741,plain,
    ( spl3_33
  <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f777,plain,(
    spl3_30 ),
    inference(avatar_contradiction_clause,[],[f775])).

fof(f775,plain,
    ( $false
    | spl3_30 ),
    inference(resolution,[],[f727,f45])).

fof(f45,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f36,f29])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f727,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f725])).

fof(f725,plain,
    ( spl3_30
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f745,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | ~ spl3_1
    | ~ spl3_33
    | spl3_5 ),
    inference(avatar_split_clause,[],[f658,f174,f741,f86,f216,f194])).

fof(f194,plain,
    ( spl3_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f216,plain,
    ( spl3_10
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f86,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f174,plain,
    ( spl3_5
  <=> r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f658,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_5 ),
    inference(resolution,[],[f176,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
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
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f176,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK2))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f174])).

fof(f728,plain,
    ( ~ spl3_1
    | ~ spl3_30
    | spl3_10 ),
    inference(avatar_split_clause,[],[f709,f216,f725,f86])).

fof(f709,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(resolution,[],[f470,f75])).

fof(f470,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_10 ),
    inference(resolution,[],[f436,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f436,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f218,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f218,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f216])).

fof(f435,plain,(
    spl3_19 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | spl3_19 ),
    inference(resolution,[],[f350,f32])).

fof(f350,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl3_19
  <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f352,plain,
    ( ~ spl3_1
    | ~ spl3_19
    | spl3_12 ),
    inference(avatar_split_clause,[],[f340,f224,f348,f86])).

fof(f224,plain,
    ( spl3_12
  <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f340,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_12 ),
    inference(superposition,[],[f226,f42])).

fof(f226,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f224])).

fof(f233,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f222,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f222,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl3_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f227,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | spl3_4 ),
    inference(avatar_split_clause,[],[f211,f170,f224,f220,f216,f194])).

fof(f170,plain,
    ( spl3_4
  <=> r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f211,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_4 ),
    inference(resolution,[],[f172,f31])).

fof(f172,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f170])).

fof(f199,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f196,f27])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f196,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f197,plain,
    ( ~ spl3_9
    | ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f191,f166,f86,f194])).

fof(f166,plain,
    ( spl3_3
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f191,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_3 ),
    inference(resolution,[],[f168,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f168,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f166])).

fof(f177,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f158,f174,f170,f166])).

fof(f158,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f76,f30])).

fof(f30,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X6,X8,X7,X9] :
      ( r1_tarski(X9,k9_subset_1(X8,X6,X7))
      | ~ r1_tarski(X9,X7)
      | ~ r1_tarski(X9,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8)) ) ),
    inference(superposition,[],[f43,f42])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f97,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f88,f29])).

fof(f88,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (6769)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (6771)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (6777)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (6779)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (6776)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (6768)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (6766)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (6778)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (6774)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (6770)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (6767)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (6775)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  % (6768)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f797,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f97,f177,f197,f199,f227,f233,f352,f435,f728,f745,f777,f796])).
% 0.22/0.52  fof(f796,plain,(
% 0.22/0.52    spl3_33),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f794])).
% 0.22/0.52  fof(f794,plain,(
% 0.22/0.52    $false | spl3_33),
% 0.22/0.52    inference(resolution,[],[f780,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ((~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f10])).
% 0.22/0.53  fof(f10,conjecture,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).
% 0.22/0.53  fof(f780,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_33),
% 0.22/0.53    inference(resolution,[],[f743,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X4,X5,X3] : (r1_tarski(k9_subset_1(X5,X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X5))) )),
% 0.22/0.53    inference(superposition,[],[f47,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f38,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 0.22/0.53    inference(superposition,[],[f32,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f33,f34,f34])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.54  fof(f743,plain,(
% 0.22/0.54    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) | spl3_33),
% 0.22/0.54    inference(avatar_component_clause,[],[f741])).
% 0.22/0.54  fof(f741,plain,(
% 0.22/0.54    spl3_33 <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.54  fof(f777,plain,(
% 0.22/0.54    spl3_30),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f775])).
% 0.22/0.54  fof(f775,plain,(
% 0.22/0.54    $false | spl3_30),
% 0.22/0.54    inference(resolution,[],[f727,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f36,f29])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f727,plain,(
% 0.22/0.54    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_30),
% 0.22/0.54    inference(avatar_component_clause,[],[f725])).
% 0.22/0.54  fof(f725,plain,(
% 0.22/0.54    spl3_30 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.54  fof(f745,plain,(
% 0.22/0.54    ~spl3_9 | ~spl3_10 | ~spl3_1 | ~spl3_33 | spl3_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f658,f174,f741,f86,f216,f194])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    spl3_9 <=> l1_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.54  fof(f216,plain,(
% 0.22/0.54    spl3_10 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    spl3_5 <=> r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.54  fof(f658,plain,(
% 0.22/0.54    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_5),
% 0.22/0.54    inference(resolution,[],[f176,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK2)) | spl3_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f174])).
% 0.22/0.54  fof(f728,plain,(
% 0.22/0.54    ~spl3_1 | ~spl3_30 | spl3_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f709,f216,f725,f86])).
% 0.22/0.54  fof(f709,plain,(
% 0.22/0.54    ~r1_tarski(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 0.22/0.54    inference(resolution,[],[f470,f75])).
% 0.22/0.54  fof(f470,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_10),
% 0.22/0.54    inference(resolution,[],[f436,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.54  fof(f436,plain,(
% 0.22/0.54    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) | spl3_10),
% 0.22/0.54    inference(resolution,[],[f218,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f218,plain,(
% 0.22/0.54    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f216])).
% 0.22/0.54  fof(f435,plain,(
% 0.22/0.54    spl3_19),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f431])).
% 0.22/0.54  fof(f431,plain,(
% 0.22/0.54    $false | spl3_19),
% 0.22/0.54    inference(resolution,[],[f350,f32])).
% 0.22/0.54  fof(f350,plain,(
% 0.22/0.54    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) | spl3_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f348])).
% 0.22/0.54  fof(f348,plain,(
% 0.22/0.54    spl3_19 <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.54  fof(f352,plain,(
% 0.22/0.54    ~spl3_1 | ~spl3_19 | spl3_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f340,f224,f348,f86])).
% 0.22/0.54  fof(f224,plain,(
% 0.22/0.54    spl3_12 <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.54  fof(f340,plain,(
% 0.22/0.54    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_12),
% 0.22/0.54    inference(superposition,[],[f226,f42])).
% 0.22/0.54  fof(f226,plain,(
% 0.22/0.54    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | spl3_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f224])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    spl3_11),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f231])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    $false | spl3_11),
% 0.22/0.54    inference(resolution,[],[f222,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f220])).
% 0.22/0.54  fof(f220,plain,(
% 0.22/0.54    spl3_11 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.54  fof(f227,plain,(
% 0.22/0.54    ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_12 | spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f211,f170,f224,f220,f216,f194])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    spl3_4 <=> r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.54  fof(f211,plain,(
% 0.22/0.54    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_4),
% 0.22/0.54    inference(resolution,[],[f172,f31])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK1)) | spl3_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f170])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    spl3_9),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f198])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    $false | spl3_9),
% 0.22/0.54    inference(resolution,[],[f196,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | spl3_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f194])).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    ~spl3_9 | ~spl3_1 | spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f191,f166,f86,f194])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    spl3_3 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_3),
% 0.22/0.54    inference(resolution,[],[f168,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f166])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f158,f174,f170,f166])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK2)) | ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(resolution,[],[f76,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X6,X8,X7,X9] : (r1_tarski(X9,k9_subset_1(X8,X6,X7)) | ~r1_tarski(X9,X7) | ~r1_tarski(X9,X6) | ~m1_subset_1(X7,k1_zfmisc_1(X8))) )),
% 0.22/0.54    inference(superposition,[],[f43,f42])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f40,f34])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    spl3_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    $false | spl3_1),
% 0.22/0.54    inference(resolution,[],[f88,f29])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f86])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (6768)------------------------------
% 0.22/0.54  % (6768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6768)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (6768)Memory used [KB]: 6524
% 0.22/0.54  % (6768)Time elapsed: 0.078 s
% 0.22/0.54  % (6768)------------------------------
% 0.22/0.54  % (6768)------------------------------
% 0.22/0.54  % (6763)Success in time 0.177 s
%------------------------------------------------------------------------------
