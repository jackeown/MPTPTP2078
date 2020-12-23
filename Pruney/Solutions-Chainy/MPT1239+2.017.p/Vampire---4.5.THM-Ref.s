%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:13 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 262 expanded)
%              Number of leaves         :   20 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  268 ( 969 expanded)
%              Number of equality atoms :    6 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f944,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f208,f225,f296,f355,f377,f385,f943])).

fof(f943,plain,
    ( spl3_16
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f942])).

fof(f942,plain,
    ( $false
    | spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f938,f168])).

fof(f168,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f165,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(f165,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f38,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f938,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl3_16
    | ~ spl3_17 ),
    inference(resolution,[],[f523,f467])).

fof(f467,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | ~ spl3_17 ),
    inference(resolution,[],[f439,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f439,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f437,f34])).

fof(f437,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_17 ),
    inference(resolution,[],[f427,f38])).

fof(f427,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f425,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f425,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(superposition,[],[f349,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f349,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl3_17
  <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f523,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),X0)
        | ~ r1_tarski(k1_tops_1(sK0,sK2),X0) )
    | spl3_16 ),
    inference(resolution,[],[f522,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,X0)
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f48,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f522,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_16 ),
    inference(subsumption_resolution,[],[f521,f35])).

fof(f521,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_16 ),
    inference(superposition,[],[f295,f50])).

fof(f295,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl3_16
  <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f385,plain,(
    spl3_18 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl3_18 ),
    inference(subsumption_resolution,[],[f383,f35])).

fof(f383,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_18 ),
    inference(subsumption_resolution,[],[f382,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f382,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_18 ),
    inference(superposition,[],[f354,f50])).

fof(f354,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl3_18
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f377,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | spl3_17 ),
    inference(subsumption_resolution,[],[f369,f57])).

fof(f57,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f45,f35])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f369,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_17 ),
    inference(resolution,[],[f361,f40])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_17 ),
    inference(resolution,[],[f360,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f53,f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f360,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_17 ),
    inference(resolution,[],[f359,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f359,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_17 ),
    inference(subsumption_resolution,[],[f358,f35])).

fof(f358,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_17 ),
    inference(superposition,[],[f350,f50])).

fof(f350,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f348])).

fof(f355,plain,
    ( ~ spl3_17
    | ~ spl3_18
    | spl3_15 ),
    inference(avatar_split_clause,[],[f346,f289,f352,f348])).

fof(f289,plain,
    ( spl3_15
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f346,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(subsumption_resolution,[],[f345,f34])).

fof(f345,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f342,f35])).

fof(f342,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_15 ),
    inference(resolution,[],[f291,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f291,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f289])).

fof(f296,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | spl3_10 ),
    inference(avatar_split_clause,[],[f285,f205,f293,f289])).

fof(f205,plain,
    ( spl3_10
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f285,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_10 ),
    inference(resolution,[],[f207,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f207,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f225,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f223,f57])).

fof(f223,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f210,f167])).

fof(f167,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f164,f34])).

fof(f164,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f38,f35])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_9 ),
    inference(resolution,[],[f209,f79])).

fof(f209,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f203,f46])).

fof(f203,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl3_9
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f208,plain,
    ( ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f198,f205,f201])).

fof(f198,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f37,f50])).

fof(f37,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:17:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.50  % (3248)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.52  % (3252)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.52  % (3241)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.52  % (3245)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (3243)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.53  % (3239)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.53  % (3242)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.54  % (3264)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.54  % (3246)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.54  % (3253)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.54  % (3259)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.54  % (3263)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.54  % (3262)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.54  % (3247)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.54  % (3254)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.54  % (3249)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.54  % (3258)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.54  % (3244)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.55  % (3240)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.55  % (3256)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.55  % (3255)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.55  % (3257)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.55  % (3250)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.56  % (3260)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.56  % (3261)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.56  % (3251)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.59/0.58  % (3243)Refutation found. Thanks to Tanya!
% 1.59/0.58  % SZS status Theorem for theBenchmark
% 1.59/0.58  % SZS output start Proof for theBenchmark
% 1.59/0.58  fof(f944,plain,(
% 1.59/0.58    $false),
% 1.59/0.58    inference(avatar_sat_refutation,[],[f208,f225,f296,f355,f377,f385,f943])).
% 1.59/0.58  fof(f943,plain,(
% 1.59/0.58    spl3_16 | ~spl3_17),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f942])).
% 1.59/0.58  fof(f942,plain,(
% 1.59/0.58    $false | (spl3_16 | ~spl3_17)),
% 1.59/0.58    inference(subsumption_resolution,[],[f938,f168])).
% 1.59/0.58  fof(f168,plain,(
% 1.59/0.58    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 1.59/0.58    inference(subsumption_resolution,[],[f165,f34])).
% 1.59/0.58  fof(f34,plain,(
% 1.59/0.58    l1_pre_topc(sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f29])).
% 1.59/0.58  fof(f29,plain,(
% 1.59/0.58    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27,f26])).
% 1.59/0.58  fof(f26,plain,(
% 1.59/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f27,plain,(
% 1.59/0.58    ? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f28,plain,(
% 1.59/0.58    ? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f15,plain,(
% 1.59/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.59/0.58    inference(flattening,[],[f14])).
% 1.59/0.58  fof(f14,plain,(
% 1.59/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f13])).
% 1.59/0.58  fof(f13,negated_conjecture,(
% 1.59/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.59/0.58    inference(negated_conjecture,[],[f12])).
% 1.59/0.58  fof(f12,conjecture,(
% 1.59/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).
% 1.59/0.58  fof(f165,plain,(
% 1.59/0.58    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 1.59/0.58    inference(resolution,[],[f38,f36])).
% 1.59/0.58  fof(f36,plain,(
% 1.59/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.58    inference(cnf_transformation,[],[f29])).
% 1.59/0.58  fof(f38,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f16])).
% 1.59/0.58  fof(f16,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f10])).
% 1.59/0.58  fof(f10,axiom,(
% 1.59/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.59/0.58  fof(f938,plain,(
% 1.59/0.58    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | (spl3_16 | ~spl3_17)),
% 1.59/0.58    inference(resolution,[],[f523,f467])).
% 1.59/0.58  fof(f467,plain,(
% 1.59/0.58    r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) | ~spl3_17),
% 1.59/0.58    inference(resolution,[],[f439,f52])).
% 1.59/0.58  fof(f52,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f22])).
% 1.59/0.58  fof(f22,plain,(
% 1.59/0.58    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.59/0.58    inference(ennf_transformation,[],[f2])).
% 1.59/0.58  fof(f2,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.59/0.58  fof(f439,plain,(
% 1.59/0.58    r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) | ~spl3_17),
% 1.59/0.58    inference(subsumption_resolution,[],[f437,f34])).
% 1.59/0.58  fof(f437,plain,(
% 1.59/0.58    r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) | ~l1_pre_topc(sK0) | ~spl3_17),
% 1.59/0.58    inference(resolution,[],[f427,f38])).
% 1.59/0.58  fof(f427,plain,(
% 1.59/0.58    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_17),
% 1.59/0.58    inference(subsumption_resolution,[],[f425,f35])).
% 1.59/0.58  fof(f35,plain,(
% 1.59/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.58    inference(cnf_transformation,[],[f29])).
% 1.59/0.58  fof(f425,plain,(
% 1.59/0.58    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_17),
% 1.59/0.58    inference(superposition,[],[f349,f50])).
% 1.59/0.58  fof(f50,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f21])).
% 1.59/0.58  fof(f21,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f8])).
% 1.59/0.58  fof(f8,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.59/0.58  fof(f349,plain,(
% 1.59/0.58    m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_17),
% 1.59/0.58    inference(avatar_component_clause,[],[f348])).
% 1.59/0.58  fof(f348,plain,(
% 1.59/0.58    spl3_17 <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.59/0.58  fof(f523,plain,(
% 1.59/0.58    ( ! [X0] : (~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),X0) | ~r1_tarski(k1_tops_1(sK0,sK2),X0)) ) | spl3_16),
% 1.59/0.58    inference(resolution,[],[f522,f60])).
% 1.59/0.58  fof(f60,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(X2,X0) | ~r1_xboole_0(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.59/0.58    inference(superposition,[],[f48,f41])).
% 1.59/0.58  fof(f41,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f19])).
% 1.59/0.58  fof(f19,plain,(
% 1.59/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f4])).
% 1.59/0.58  fof(f4,axiom,(
% 1.59/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.59/0.58  fof(f48,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f20])).
% 1.59/0.58  fof(f20,plain,(
% 1.59/0.58    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.59/0.58    inference(ennf_transformation,[],[f6])).
% 1.59/0.58  fof(f6,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.59/0.58  fof(f522,plain,(
% 1.59/0.58    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_16),
% 1.59/0.58    inference(subsumption_resolution,[],[f521,f35])).
% 1.59/0.58  fof(f521,plain,(
% 1.59/0.58    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_16),
% 1.59/0.58    inference(superposition,[],[f295,f50])).
% 1.59/0.58  fof(f295,plain,(
% 1.59/0.58    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_16),
% 1.59/0.58    inference(avatar_component_clause,[],[f293])).
% 1.59/0.58  fof(f293,plain,(
% 1.59/0.58    spl3_16 <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.59/0.58  fof(f385,plain,(
% 1.59/0.58    spl3_18),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f384])).
% 1.59/0.58  fof(f384,plain,(
% 1.59/0.58    $false | spl3_18),
% 1.59/0.58    inference(subsumption_resolution,[],[f383,f35])).
% 1.59/0.58  fof(f383,plain,(
% 1.59/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_18),
% 1.59/0.58    inference(subsumption_resolution,[],[f382,f40])).
% 1.59/0.58  fof(f40,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f5])).
% 1.59/0.58  fof(f5,axiom,(
% 1.59/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.59/0.58  fof(f382,plain,(
% 1.59/0.58    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_18),
% 1.59/0.58    inference(superposition,[],[f354,f50])).
% 1.59/0.58  fof(f354,plain,(
% 1.59/0.58    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | spl3_18),
% 1.59/0.58    inference(avatar_component_clause,[],[f352])).
% 1.59/0.58  fof(f352,plain,(
% 1.59/0.58    spl3_18 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.59/0.58  fof(f377,plain,(
% 1.59/0.58    spl3_17),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f376])).
% 1.59/0.58  fof(f376,plain,(
% 1.59/0.58    $false | spl3_17),
% 1.59/0.58    inference(subsumption_resolution,[],[f369,f57])).
% 1.59/0.58  fof(f57,plain,(
% 1.59/0.58    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.59/0.58    inference(resolution,[],[f45,f35])).
% 1.59/0.58  fof(f45,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f32])).
% 1.59/0.58  fof(f32,plain,(
% 1.59/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.59/0.58    inference(nnf_transformation,[],[f9])).
% 1.59/0.58  fof(f9,axiom,(
% 1.59/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.59/0.58  fof(f369,plain,(
% 1.59/0.58    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_17),
% 1.59/0.58    inference(resolution,[],[f361,f40])).
% 1.59/0.58  fof(f361,plain,(
% 1.59/0.58    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK1,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_17),
% 1.59/0.58    inference(resolution,[],[f360,f79])).
% 1.59/0.58  fof(f79,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.59/0.58    inference(superposition,[],[f53,f41])).
% 1.59/0.58  fof(f53,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f23])).
% 1.59/0.58  fof(f23,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.59/0.58    inference(ennf_transformation,[],[f3])).
% 1.59/0.58  fof(f3,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.59/0.58  fof(f360,plain,(
% 1.59/0.58    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_17),
% 1.59/0.58    inference(resolution,[],[f359,f46])).
% 1.59/0.58  fof(f46,plain,(
% 1.59/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f32])).
% 1.59/0.58  fof(f359,plain,(
% 1.59/0.58    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_17),
% 1.59/0.58    inference(subsumption_resolution,[],[f358,f35])).
% 1.59/0.58  fof(f358,plain,(
% 1.59/0.58    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_17),
% 1.59/0.58    inference(superposition,[],[f350,f50])).
% 1.59/0.58  fof(f350,plain,(
% 1.59/0.58    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_17),
% 1.59/0.58    inference(avatar_component_clause,[],[f348])).
% 1.59/0.58  fof(f355,plain,(
% 1.59/0.58    ~spl3_17 | ~spl3_18 | spl3_15),
% 1.59/0.58    inference(avatar_split_clause,[],[f346,f289,f352,f348])).
% 1.59/0.58  fof(f289,plain,(
% 1.59/0.58    spl3_15 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.59/0.58  fof(f346,plain,(
% 1.59/0.58    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 1.59/0.58    inference(subsumption_resolution,[],[f345,f34])).
% 1.59/0.58  fof(f345,plain,(
% 1.59/0.58    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_15),
% 1.59/0.58    inference(subsumption_resolution,[],[f342,f35])).
% 1.59/0.58  fof(f342,plain,(
% 1.59/0.58    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_15),
% 1.59/0.58    inference(resolution,[],[f291,f39])).
% 1.59/0.58  fof(f39,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f18])).
% 1.59/0.58  fof(f18,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(flattening,[],[f17])).
% 1.59/0.58  fof(f17,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f11])).
% 1.59/0.58  fof(f11,axiom,(
% 1.59/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 1.59/0.58  fof(f291,plain,(
% 1.59/0.58    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_15),
% 1.59/0.58    inference(avatar_component_clause,[],[f289])).
% 1.59/0.58  fof(f296,plain,(
% 1.59/0.58    ~spl3_15 | ~spl3_16 | spl3_10),
% 1.59/0.58    inference(avatar_split_clause,[],[f285,f205,f293,f289])).
% 1.59/0.58  fof(f205,plain,(
% 1.59/0.58    spl3_10 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.59/0.58  fof(f285,plain,(
% 1.59/0.58    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_10),
% 1.59/0.58    inference(resolution,[],[f207,f54])).
% 1.59/0.58  fof(f54,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f25])).
% 1.59/0.58  fof(f25,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.59/0.58    inference(flattening,[],[f24])).
% 1.59/0.58  fof(f24,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.59/0.58    inference(ennf_transformation,[],[f7])).
% 1.59/0.58  fof(f7,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.59/0.58  fof(f207,plain,(
% 1.59/0.58    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_10),
% 1.59/0.58    inference(avatar_component_clause,[],[f205])).
% 1.59/0.58  fof(f225,plain,(
% 1.59/0.58    spl3_9),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f224])).
% 1.59/0.58  fof(f224,plain,(
% 1.59/0.58    $false | spl3_9),
% 1.59/0.58    inference(subsumption_resolution,[],[f223,f57])).
% 1.59/0.58  fof(f223,plain,(
% 1.59/0.58    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_9),
% 1.59/0.58    inference(resolution,[],[f210,f167])).
% 1.59/0.58  fof(f167,plain,(
% 1.59/0.58    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.59/0.58    inference(subsumption_resolution,[],[f164,f34])).
% 1.59/0.58  fof(f164,plain,(
% 1.59/0.58    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 1.59/0.58    inference(resolution,[],[f38,f35])).
% 1.59/0.58  fof(f210,plain,(
% 1.59/0.58    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_9),
% 1.59/0.58    inference(resolution,[],[f209,f79])).
% 1.59/0.58  fof(f209,plain,(
% 1.59/0.58    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_9),
% 1.59/0.58    inference(resolution,[],[f203,f46])).
% 1.59/0.58  fof(f203,plain,(
% 1.59/0.58    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 1.59/0.58    inference(avatar_component_clause,[],[f201])).
% 1.59/0.58  fof(f201,plain,(
% 1.59/0.58    spl3_9 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.59/0.58  fof(f208,plain,(
% 1.59/0.58    ~spl3_9 | ~spl3_10),
% 1.59/0.58    inference(avatar_split_clause,[],[f198,f205,f201])).
% 1.59/0.58  fof(f198,plain,(
% 1.59/0.58    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.58    inference(superposition,[],[f37,f50])).
% 1.59/0.58  fof(f37,plain,(
% 1.59/0.58    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.59/0.58    inference(cnf_transformation,[],[f29])).
% 1.59/0.58  % SZS output end Proof for theBenchmark
% 1.59/0.58  % (3243)------------------------------
% 1.59/0.58  % (3243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (3243)Termination reason: Refutation
% 1.59/0.58  
% 1.59/0.58  % (3243)Memory used [KB]: 6524
% 1.59/0.58  % (3243)Time elapsed: 0.155 s
% 1.59/0.58  % (3243)------------------------------
% 1.59/0.58  % (3243)------------------------------
% 1.59/0.58  % (3238)Success in time 0.213 s
%------------------------------------------------------------------------------
