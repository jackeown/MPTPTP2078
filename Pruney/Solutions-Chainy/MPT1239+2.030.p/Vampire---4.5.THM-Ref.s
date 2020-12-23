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
% DateTime   : Thu Dec  3 13:11:15 EST 2020

% Result     : Theorem 1.08s
% Output     : Refutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 187 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :    8
%              Number of atoms          :  279 ( 527 expanded)
%              Number of equality atoms :    9 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f630,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f102,f152,f224,f235,f359,f375,f378,f420,f565,f610,f629])).

fof(f629,plain,
    ( ~ spl3_3
    | spl3_38 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | ~ spl3_3
    | spl3_38 ),
    inference(resolution,[],[f620,f99])).

fof(f99,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_3
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f620,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl3_38 ),
    inference(resolution,[],[f609,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f56,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X1,X2))),X1) ),
    inference(resolution,[],[f46,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f609,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f607])).

fof(f607,plain,
    ( spl3_38
  <=> r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f610,plain,
    ( ~ spl3_4
    | ~ spl3_38
    | spl3_34 ),
    inference(avatar_split_clause,[],[f600,f562,f607,f143])).

fof(f143,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f562,plain,
    ( spl3_34
  <=> r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f600,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_34 ),
    inference(superposition,[],[f564,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f564,plain,
    ( ~ r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_1(sK0,sK2))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f562])).

fof(f565,plain,
    ( ~ spl3_4
    | ~ spl3_1
    | ~ spl3_34
    | spl3_8 ),
    inference(avatar_split_clause,[],[f546,f221,f562,f88,f143])).

fof(f88,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f221,plain,
    ( spl3_8
  <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f546,plain,
    ( ~ r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(resolution,[],[f426,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f426,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X3)
        | ~ r1_xboole_0(X3,k1_tops_1(sK0,sK2)) )
    | spl3_8 ),
    inference(resolution,[],[f223,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f223,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f221])).

fof(f420,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | spl3_15 ),
    inference(resolution,[],[f379,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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

fof(f32,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(f379,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(resolution,[],[f328,f48])).

fof(f328,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl3_15
  <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f378,plain,(
    spl3_19 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | spl3_19 ),
    inference(resolution,[],[f358,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f358,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl3_19
  <=> r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f375,plain,
    ( ~ spl3_1
    | ~ spl3_15
    | ~ spl3_4
    | ~ spl3_16
    | spl3_7 ),
    inference(avatar_split_clause,[],[f321,f217,f330,f143,f326,f88])).

fof(f330,plain,
    ( spl3_16
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f217,plain,
    ( spl3_7
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f321,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_7 ),
    inference(resolution,[],[f219,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f219,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f217])).

fof(f359,plain,
    ( ~ spl3_4
    | ~ spl3_19
    | spl3_16 ),
    inference(avatar_split_clause,[],[f349,f330,f356,f143])).

fof(f349,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_16 ),
    inference(superposition,[],[f332,f54])).

fof(f332,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f330])).

fof(f235,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f234,f213,f143,f88])).

fof(f213,plain,
    ( spl3_6
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f234,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_6 ),
    inference(resolution,[],[f215,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f215,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f213])).

fof(f224,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f206,f221,f217,f213])).

fof(f206,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f133,f37])).

fof(f37,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k7_subset_1(X2,X0,X1))
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_tarski(X3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f55,f54])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f42])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f152,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f145,f35])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f102,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f90,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f100,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f85,f97,f88])).

fof(f85,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f38,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (819593217)
% 0.13/0.37  ipcrm: permission denied for id (819691524)
% 0.13/0.37  ipcrm: permission denied for id (819789830)
% 0.13/0.37  ipcrm: permission denied for id (819822599)
% 0.13/0.37  ipcrm: permission denied for id (819920906)
% 0.13/0.38  ipcrm: permission denied for id (820051984)
% 0.13/0.39  ipcrm: permission denied for id (820183061)
% 0.13/0.39  ipcrm: permission denied for id (820281369)
% 0.13/0.39  ipcrm: permission denied for id (820314138)
% 0.13/0.39  ipcrm: permission denied for id (820346907)
% 0.13/0.40  ipcrm: permission denied for id (820379676)
% 0.13/0.40  ipcrm: permission denied for id (820445215)
% 0.20/0.41  ipcrm: permission denied for id (820707368)
% 0.20/0.42  ipcrm: permission denied for id (820871213)
% 0.20/0.42  ipcrm: permission denied for id (820903982)
% 0.20/0.42  ipcrm: permission denied for id (820969520)
% 0.20/0.42  ipcrm: permission denied for id (821002289)
% 0.20/0.42  ipcrm: permission denied for id (821067827)
% 0.20/0.43  ipcrm: permission denied for id (821133365)
% 0.20/0.43  ipcrm: permission denied for id (821198903)
% 0.20/0.43  ipcrm: permission denied for id (821264441)
% 0.20/0.44  ipcrm: permission denied for id (821329981)
% 0.20/0.44  ipcrm: permission denied for id (821395519)
% 0.20/0.44  ipcrm: permission denied for id (821428289)
% 0.20/0.44  ipcrm: permission denied for id (821493827)
% 0.20/0.45  ipcrm: permission denied for id (821526597)
% 0.20/0.45  ipcrm: permission denied for id (821559366)
% 0.20/0.45  ipcrm: permission denied for id (821592135)
% 0.20/0.45  ipcrm: permission denied for id (821657673)
% 0.20/0.45  ipcrm: permission denied for id (821690442)
% 0.20/0.45  ipcrm: permission denied for id (821723211)
% 0.20/0.46  ipcrm: permission denied for id (821788750)
% 0.20/0.46  ipcrm: permission denied for id (821854288)
% 0.20/0.46  ipcrm: permission denied for id (821985364)
% 0.20/0.46  ipcrm: permission denied for id (822018133)
% 0.20/0.47  ipcrm: permission denied for id (822083671)
% 0.20/0.47  ipcrm: permission denied for id (822116440)
% 0.20/0.47  ipcrm: permission denied for id (822149209)
% 0.20/0.47  ipcrm: permission denied for id (822181978)
% 0.20/0.48  ipcrm: permission denied for id (822280286)
% 0.20/0.48  ipcrm: permission denied for id (822345824)
% 0.20/0.48  ipcrm: permission denied for id (822411362)
% 0.20/0.48  ipcrm: permission denied for id (822476902)
% 0.20/0.49  ipcrm: permission denied for id (822509671)
% 0.20/0.49  ipcrm: permission denied for id (822607979)
% 0.20/0.49  ipcrm: permission denied for id (822673517)
% 0.20/0.49  ipcrm: permission denied for id (822706286)
% 0.20/0.50  ipcrm: permission denied for id (822771824)
% 0.20/0.50  ipcrm: permission denied for id (822870131)
% 0.20/0.50  ipcrm: permission denied for id (822968437)
% 0.20/0.51  ipcrm: permission denied for id (823033975)
% 0.20/0.51  ipcrm: permission denied for id (823099513)
% 0.20/0.51  ipcrm: permission denied for id (823132282)
% 0.20/0.51  ipcrm: permission denied for id (823230591)
% 0.20/0.57  % (6831)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.99/0.62  % (6837)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.99/0.62  % (6835)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.08/0.63  % (6829)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.08/0.63  % (6833)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.08/0.63  % (6834)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.08/0.63  % (6825)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.08/0.63  % (6820)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.08/0.63  % (6828)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.08/0.64  % (6823)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.08/0.65  % (6830)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.08/0.65  % (6824)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.08/0.65  % (6832)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.08/0.65  % (6826)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.08/0.65  % (6822)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.08/0.65  % (6836)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.08/0.66  % (6827)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.08/0.66  % (6824)Refutation found. Thanks to Tanya!
% 1.08/0.66  % SZS status Theorem for theBenchmark
% 1.08/0.66  % SZS output start Proof for theBenchmark
% 1.08/0.66  fof(f630,plain,(
% 1.08/0.66    $false),
% 1.08/0.66    inference(avatar_sat_refutation,[],[f100,f102,f152,f224,f235,f359,f375,f378,f420,f565,f610,f629])).
% 1.08/0.66  fof(f629,plain,(
% 1.08/0.66    ~spl3_3 | spl3_38),
% 1.08/0.66    inference(avatar_contradiction_clause,[],[f628])).
% 1.08/0.66  fof(f628,plain,(
% 1.08/0.66    $false | (~spl3_3 | spl3_38)),
% 1.08/0.66    inference(resolution,[],[f620,f99])).
% 1.08/0.66  fof(f99,plain,(
% 1.08/0.66    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl3_3),
% 1.08/0.66    inference(avatar_component_clause,[],[f97])).
% 1.08/0.66  fof(f97,plain,(
% 1.08/0.66    spl3_3 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 1.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.08/0.66  fof(f620,plain,(
% 1.08/0.66    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | spl3_38),
% 1.08/0.66    inference(resolution,[],[f609,f64])).
% 1.08/0.66  fof(f64,plain,(
% 1.08/0.66    ( ! [X2,X0,X1] : (r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X0) | ~r1_tarski(X0,X1)) )),
% 1.08/0.66    inference(superposition,[],[f56,f43])).
% 1.08/0.66  fof(f43,plain,(
% 1.08/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.08/0.66    inference(cnf_transformation,[],[f20])).
% 1.08/0.66  fof(f20,plain,(
% 1.08/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.08/0.66    inference(ennf_transformation,[],[f2])).
% 1.08/0.66  fof(f2,axiom,(
% 1.08/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.08/0.66  fof(f56,plain,(
% 1.08/0.66    ( ! [X2,X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X1,X2))),X1)) )),
% 1.08/0.66    inference(resolution,[],[f46,f53])).
% 1.08/0.66  fof(f53,plain,(
% 1.08/0.66    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.08/0.66    inference(definition_unfolding,[],[f41,f42])).
% 1.08/0.66  fof(f42,plain,(
% 1.08/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.08/0.66    inference(cnf_transformation,[],[f1])).
% 1.08/0.66  fof(f1,axiom,(
% 1.08/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.08/0.66  fof(f41,plain,(
% 1.08/0.66    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.08/0.66    inference(cnf_transformation,[],[f6])).
% 1.08/0.66  fof(f6,axiom,(
% 1.08/0.66    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.08/0.66  fof(f46,plain,(
% 1.08/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.08/0.66    inference(cnf_transformation,[],[f23])).
% 1.08/0.66  fof(f23,plain,(
% 1.08/0.66    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.08/0.66    inference(ennf_transformation,[],[f5])).
% 1.08/0.66  fof(f5,axiom,(
% 1.08/0.66    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.08/0.66  fof(f609,plain,(
% 1.08/0.66    ~r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_38),
% 1.08/0.66    inference(avatar_component_clause,[],[f607])).
% 1.08/0.66  fof(f607,plain,(
% 1.08/0.66    spl3_38 <=> r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 1.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.08/0.66  fof(f610,plain,(
% 1.08/0.66    ~spl3_4 | ~spl3_38 | spl3_34),
% 1.08/0.66    inference(avatar_split_clause,[],[f600,f562,f607,f143])).
% 1.08/0.66  fof(f143,plain,(
% 1.08/0.66    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.08/0.66  fof(f562,plain,(
% 1.08/0.66    spl3_34 <=> r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_1(sK0,sK2))),
% 1.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.08/0.66  fof(f600,plain,(
% 1.08/0.66    ~r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_34),
% 1.08/0.66    inference(superposition,[],[f564,f54])).
% 1.08/0.66  fof(f54,plain,(
% 1.08/0.66    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.08/0.66    inference(definition_unfolding,[],[f49,f42])).
% 1.08/0.66  fof(f49,plain,(
% 1.08/0.66    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.08/0.66    inference(cnf_transformation,[],[f25])).
% 1.08/0.66  fof(f25,plain,(
% 1.08/0.66    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.08/0.66    inference(ennf_transformation,[],[f9])).
% 1.08/0.66  fof(f9,axiom,(
% 1.08/0.66    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.08/0.66  fof(f564,plain,(
% 1.08/0.66    ~r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_1(sK0,sK2)) | spl3_34),
% 1.08/0.66    inference(avatar_component_clause,[],[f562])).
% 1.08/0.66  fof(f565,plain,(
% 1.08/0.66    ~spl3_4 | ~spl3_1 | ~spl3_34 | spl3_8),
% 1.08/0.66    inference(avatar_split_clause,[],[f546,f221,f562,f88,f143])).
% 1.08/0.66  fof(f88,plain,(
% 1.08/0.66    spl3_1 <=> l1_pre_topc(sK0)),
% 1.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.08/0.66  fof(f221,plain,(
% 1.08/0.66    spl3_8 <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))),
% 1.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.08/0.66  fof(f546,plain,(
% 1.08/0.66    ~r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_8),
% 1.08/0.66    inference(resolution,[],[f426,f86])).
% 1.08/0.66  fof(f86,plain,(
% 1.08/0.66    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),X1,X2)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.08/0.66    inference(resolution,[],[f38,f48])).
% 1.08/0.66  fof(f48,plain,(
% 1.08/0.66    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.08/0.66    inference(cnf_transformation,[],[f24])).
% 1.08/0.66  fof(f24,plain,(
% 1.08/0.66    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.08/0.66    inference(ennf_transformation,[],[f8])).
% 1.08/0.66  fof(f8,axiom,(
% 1.08/0.66    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 1.08/0.66  fof(f38,plain,(
% 1.08/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.08/0.66    inference(cnf_transformation,[],[f17])).
% 1.08/0.66  fof(f17,plain,(
% 1.08/0.66    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.08/0.66    inference(ennf_transformation,[],[f11])).
% 1.08/0.66  fof(f11,axiom,(
% 1.08/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.08/0.66  fof(f426,plain,(
% 1.08/0.66    ( ! [X3] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X3) | ~r1_xboole_0(X3,k1_tops_1(sK0,sK2))) ) | spl3_8),
% 1.08/0.66    inference(resolution,[],[f223,f50])).
% 1.08/0.66  fof(f50,plain,(
% 1.08/0.66    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.08/0.66    inference(cnf_transformation,[],[f27])).
% 1.08/0.66  fof(f27,plain,(
% 1.08/0.66    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.08/0.66    inference(flattening,[],[f26])).
% 1.08/0.66  fof(f26,plain,(
% 1.08/0.66    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.08/0.66    inference(ennf_transformation,[],[f4])).
% 1.08/0.66  fof(f4,axiom,(
% 1.08/0.66    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.08/0.66  fof(f223,plain,(
% 1.08/0.66    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_8),
% 1.08/0.66    inference(avatar_component_clause,[],[f221])).
% 1.08/0.66  fof(f420,plain,(
% 1.08/0.66    spl3_15),
% 1.08/0.66    inference(avatar_contradiction_clause,[],[f419])).
% 1.08/0.66  fof(f419,plain,(
% 1.08/0.66    $false | spl3_15),
% 1.08/0.66    inference(resolution,[],[f379,f35])).
% 1.08/0.66  fof(f35,plain,(
% 1.08/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.08/0.66    inference(cnf_transformation,[],[f33])).
% 1.08/0.66  fof(f33,plain,(
% 1.08/0.66    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.08/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f32,f31,f30])).
% 1.08/0.66  fof(f30,plain,(
% 1.08/0.66    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.08/0.66    introduced(choice_axiom,[])).
% 1.08/0.66  fof(f31,plain,(
% 1.08/0.66    ? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.08/0.66    introduced(choice_axiom,[])).
% 1.08/0.66  fof(f32,plain,(
% 1.08/0.66    ? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.08/0.66    introduced(choice_axiom,[])).
% 1.08/0.66  fof(f16,plain,(
% 1.08/0.66    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.08/0.66    inference(ennf_transformation,[],[f15])).
% 1.08/0.66  fof(f15,plain,(
% 1.08/0.66    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.08/0.66    inference(pure_predicate_removal,[],[f14])).
% 1.08/0.66  fof(f14,negated_conjecture,(
% 1.08/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.08/0.66    inference(negated_conjecture,[],[f13])).
% 1.08/0.66  fof(f13,conjecture,(
% 1.08/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).
% 1.08/0.66  fof(f379,plain,(
% 1.08/0.66    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 1.08/0.66    inference(resolution,[],[f328,f48])).
% 1.08/0.66  fof(f328,plain,(
% 1.08/0.66    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 1.08/0.66    inference(avatar_component_clause,[],[f326])).
% 1.08/0.66  fof(f326,plain,(
% 1.08/0.66    spl3_15 <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.08/0.66  fof(f378,plain,(
% 1.08/0.66    spl3_19),
% 1.08/0.66    inference(avatar_contradiction_clause,[],[f376])).
% 1.08/0.66  fof(f376,plain,(
% 1.08/0.66    $false | spl3_19),
% 1.08/0.66    inference(resolution,[],[f358,f52])).
% 1.08/0.66  fof(f52,plain,(
% 1.08/0.66    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.08/0.66    inference(definition_unfolding,[],[f40,f42])).
% 1.08/0.66  fof(f40,plain,(
% 1.08/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.08/0.66    inference(cnf_transformation,[],[f3])).
% 1.08/0.66  fof(f3,axiom,(
% 1.08/0.66    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.08/0.66  fof(f358,plain,(
% 1.08/0.66    ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) | spl3_19),
% 1.08/0.66    inference(avatar_component_clause,[],[f356])).
% 1.08/0.66  fof(f356,plain,(
% 1.08/0.66    spl3_19 <=> r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),
% 1.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.08/0.66  fof(f375,plain,(
% 1.08/0.66    ~spl3_1 | ~spl3_15 | ~spl3_4 | ~spl3_16 | spl3_7),
% 1.08/0.66    inference(avatar_split_clause,[],[f321,f217,f330,f143,f326,f88])).
% 1.08/0.66  fof(f330,plain,(
% 1.08/0.66    spl3_16 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)),
% 1.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.08/0.66  fof(f217,plain,(
% 1.08/0.66    spl3_7 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))),
% 1.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.08/0.66  fof(f321,plain,(
% 1.08/0.66    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_7),
% 1.08/0.66    inference(resolution,[],[f219,f39])).
% 1.08/0.66  fof(f39,plain,(
% 1.08/0.66    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.08/0.66    inference(cnf_transformation,[],[f19])).
% 1.08/0.66  fof(f19,plain,(
% 1.08/0.66    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.08/0.66    inference(flattening,[],[f18])).
% 1.08/0.66  fof(f18,plain,(
% 1.08/0.66    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.08/0.66    inference(ennf_transformation,[],[f12])).
% 1.08/0.66  fof(f12,axiom,(
% 1.08/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.08/0.66  fof(f219,plain,(
% 1.08/0.66    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_7),
% 1.08/0.66    inference(avatar_component_clause,[],[f217])).
% 1.08/0.66  fof(f359,plain,(
% 1.08/0.66    ~spl3_4 | ~spl3_19 | spl3_16),
% 1.08/0.66    inference(avatar_split_clause,[],[f349,f330,f356,f143])).
% 1.08/0.66  fof(f349,plain,(
% 1.08/0.66    ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_16),
% 1.08/0.66    inference(superposition,[],[f332,f54])).
% 1.08/0.66  fof(f332,plain,(
% 1.08/0.66    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | spl3_16),
% 1.08/0.66    inference(avatar_component_clause,[],[f330])).
% 1.08/0.66  fof(f235,plain,(
% 1.08/0.66    ~spl3_1 | ~spl3_4 | spl3_6),
% 1.08/0.66    inference(avatar_split_clause,[],[f234,f213,f143,f88])).
% 1.08/0.66  fof(f213,plain,(
% 1.08/0.66    spl3_6 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.08/0.66  fof(f234,plain,(
% 1.08/0.66    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_6),
% 1.08/0.66    inference(resolution,[],[f215,f44])).
% 1.08/0.66  fof(f44,plain,(
% 1.08/0.66    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.08/0.66    inference(cnf_transformation,[],[f22])).
% 1.08/0.66  fof(f22,plain,(
% 1.08/0.66    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.08/0.66    inference(flattening,[],[f21])).
% 1.08/0.66  fof(f21,plain,(
% 1.08/0.66    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.08/0.66    inference(ennf_transformation,[],[f10])).
% 1.08/0.66  fof(f10,axiom,(
% 1.08/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.08/0.66  fof(f215,plain,(
% 1.08/0.66    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_6),
% 1.08/0.66    inference(avatar_component_clause,[],[f213])).
% 1.08/0.66  fof(f224,plain,(
% 1.08/0.66    ~spl3_6 | ~spl3_7 | ~spl3_8),
% 1.08/0.66    inference(avatar_split_clause,[],[f206,f221,f217,f213])).
% 1.08/0.66  fof(f206,plain,(
% 1.08/0.66    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.08/0.66    inference(resolution,[],[f133,f37])).
% 1.08/0.66  fof(f37,plain,(
% 1.08/0.66    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.08/0.66    inference(cnf_transformation,[],[f33])).
% 1.08/0.66  fof(f133,plain,(
% 1.08/0.66    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k7_subset_1(X2,X0,X1)) | ~r1_xboole_0(X3,X1) | ~r1_tarski(X3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2))) )),
% 1.08/0.66    inference(superposition,[],[f55,f54])).
% 1.08/0.66  fof(f55,plain,(
% 1.08/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.08/0.66    inference(definition_unfolding,[],[f51,f42])).
% 1.08/0.66  fof(f51,plain,(
% 1.08/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.08/0.66    inference(cnf_transformation,[],[f29])).
% 1.08/0.66  fof(f29,plain,(
% 1.08/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.08/0.66    inference(flattening,[],[f28])).
% 1.08/0.66  fof(f28,plain,(
% 1.08/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.08/0.66    inference(ennf_transformation,[],[f7])).
% 1.08/0.66  fof(f7,axiom,(
% 1.08/0.66    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.08/0.66  fof(f152,plain,(
% 1.08/0.66    spl3_4),
% 1.08/0.66    inference(avatar_contradiction_clause,[],[f151])).
% 1.08/0.66  fof(f151,plain,(
% 1.08/0.66    $false | spl3_4),
% 1.08/0.66    inference(resolution,[],[f145,f35])).
% 1.08/0.66  fof(f145,plain,(
% 1.08/0.66    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_4),
% 1.08/0.66    inference(avatar_component_clause,[],[f143])).
% 1.08/0.66  fof(f102,plain,(
% 1.08/0.66    spl3_1),
% 1.08/0.66    inference(avatar_contradiction_clause,[],[f101])).
% 1.08/0.66  fof(f101,plain,(
% 1.08/0.66    $false | spl3_1),
% 1.08/0.66    inference(resolution,[],[f90,f34])).
% 1.08/0.66  fof(f34,plain,(
% 1.08/0.66    l1_pre_topc(sK0)),
% 1.08/0.66    inference(cnf_transformation,[],[f33])).
% 1.08/0.66  fof(f90,plain,(
% 1.08/0.66    ~l1_pre_topc(sK0) | spl3_1),
% 1.08/0.66    inference(avatar_component_clause,[],[f88])).
% 1.08/0.66  fof(f100,plain,(
% 1.08/0.66    ~spl3_1 | spl3_3),
% 1.08/0.66    inference(avatar_split_clause,[],[f85,f97,f88])).
% 1.08/0.66  fof(f85,plain,(
% 1.08/0.66    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 1.08/0.66    inference(resolution,[],[f38,f36])).
% 1.08/0.66  fof(f36,plain,(
% 1.08/0.66    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.08/0.66    inference(cnf_transformation,[],[f33])).
% 1.08/0.66  % SZS output end Proof for theBenchmark
% 1.08/0.66  % (6824)------------------------------
% 1.08/0.66  % (6824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.66  % (6824)Termination reason: Refutation
% 1.08/0.66  
% 1.08/0.66  % (6824)Memory used [KB]: 6396
% 1.08/0.66  % (6824)Time elapsed: 0.090 s
% 1.08/0.66  % (6824)------------------------------
% 1.08/0.66  % (6824)------------------------------
% 1.08/0.66  % (6821)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.08/0.67  % (6686)Success in time 0.31 s
%------------------------------------------------------------------------------
