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
% DateTime   : Thu Dec  3 13:11:07 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 251 expanded)
%              Number of leaves         :   18 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  265 ( 912 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f145,f206,f247,f301,f313])).

fof(f313,plain,
    ( spl3_10
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | spl3_10
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f306,f303])).

fof(f303,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f302,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
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
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

fof(f302,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f297,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f297,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(superposition,[],[f236,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f236,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl3_14
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f306,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(subsumption_resolution,[],[f305,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f305,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(subsumption_resolution,[],[f304,f31])).

fof(f304,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(subsumption_resolution,[],[f294,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f294,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(resolution,[],[f201,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
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
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f201,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl3_10
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f301,plain,
    ( spl3_11
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl3_11
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f299,f31])).

fof(f299,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f298,f32])).

fof(f298,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f297,f227])).

fof(f227,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(subsumption_resolution,[],[f226,f30])).

fof(f226,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_11 ),
    inference(subsumption_resolution,[],[f225,f32])).

fof(f225,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_11 ),
    inference(subsumption_resolution,[],[f222,f74])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f51,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0))
      | r1_tarski(X2,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f41,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f222,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_11 ),
    inference(resolution,[],[f205,f34])).

fof(f205,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl3_11
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f247,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl3_14 ),
    inference(subsumption_resolution,[],[f245,f31])).

fof(f245,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_14 ),
    inference(subsumption_resolution,[],[f243,f32])).

fof(f243,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_14 ),
    inference(resolution,[],[f237,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f237,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f235])).

fof(f206,plain,
    ( ~ spl3_10
    | ~ spl3_11
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f193,f128,f124,f203,f199])).

fof(f124,plain,
    ( spl3_1
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f128,plain,
    ( spl3_2
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f193,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f150,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f150,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f149,f125])).

fof(f125,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f149,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f146,f129])).

fof(f129,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f146,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f137,f44])).

fof(f137,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f136,f31])).

fof(f136,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f120,f32])).

fof(f120,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f33,f44])).

fof(f33,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f145,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f143,f30])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f142,f32])).

fof(f142,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_2 ),
    inference(resolution,[],[f130,f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f130,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f141,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f139,f30])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f138,f31])).

fof(f138,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(resolution,[],[f126,f37])).

fof(f126,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f124])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 13:08:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (798752768)
% 0.21/0.37  ipcrm: permission denied for id (803995650)
% 0.21/0.37  ipcrm: permission denied for id (800489475)
% 0.21/0.37  ipcrm: permission denied for id (800555013)
% 0.21/0.38  ipcrm: permission denied for id (800620551)
% 0.21/0.38  ipcrm: permission denied for id (800686089)
% 0.21/0.38  ipcrm: permission denied for id (798851082)
% 0.21/0.38  ipcrm: permission denied for id (800718859)
% 0.21/0.38  ipcrm: permission denied for id (800751628)
% 0.21/0.38  ipcrm: permission denied for id (798916621)
% 0.21/0.38  ipcrm: permission denied for id (800784398)
% 0.21/0.39  ipcrm: permission denied for id (800817167)
% 0.21/0.39  ipcrm: permission denied for id (800849936)
% 0.21/0.39  ipcrm: permission denied for id (800948243)
% 0.21/0.39  ipcrm: permission denied for id (799014932)
% 0.21/0.39  ipcrm: permission denied for id (799047701)
% 0.21/0.39  ipcrm: permission denied for id (800981014)
% 0.21/0.40  ipcrm: permission denied for id (801013783)
% 0.21/0.40  ipcrm: permission denied for id (804192280)
% 0.21/0.40  ipcrm: permission denied for id (801079321)
% 0.21/0.40  ipcrm: permission denied for id (801112090)
% 0.21/0.40  ipcrm: permission denied for id (799113243)
% 0.21/0.40  ipcrm: permission denied for id (799146012)
% 0.21/0.40  ipcrm: permission denied for id (804225053)
% 0.21/0.41  ipcrm: permission denied for id (801177630)
% 0.21/0.41  ipcrm: permission denied for id (804257823)
% 0.21/0.41  ipcrm: permission denied for id (804290592)
% 0.21/0.41  ipcrm: permission denied for id (801275937)
% 0.21/0.41  ipcrm: permission denied for id (801308706)
% 0.21/0.41  ipcrm: permission denied for id (804323363)
% 0.21/0.41  ipcrm: permission denied for id (801374244)
% 0.21/0.41  ipcrm: permission denied for id (801407013)
% 0.21/0.42  ipcrm: permission denied for id (799277095)
% 0.21/0.42  ipcrm: permission denied for id (801472552)
% 0.21/0.42  ipcrm: permission denied for id (804388905)
% 0.21/0.42  ipcrm: permission denied for id (799375402)
% 0.21/0.42  ipcrm: permission denied for id (804421675)
% 0.21/0.43  ipcrm: permission denied for id (799440940)
% 0.21/0.43  ipcrm: permission denied for id (801570861)
% 0.21/0.43  ipcrm: permission denied for id (799473710)
% 0.21/0.43  ipcrm: permission denied for id (801603631)
% 0.21/0.43  ipcrm: permission denied for id (804454448)
% 0.21/0.43  ipcrm: permission denied for id (799539249)
% 0.21/0.44  ipcrm: permission denied for id (799572018)
% 0.21/0.44  ipcrm: permission denied for id (804519988)
% 0.21/0.44  ipcrm: permission denied for id (804552757)
% 0.21/0.44  ipcrm: permission denied for id (801767478)
% 0.21/0.45  ipcrm: permission denied for id (801833016)
% 0.21/0.45  ipcrm: permission denied for id (801865785)
% 0.21/0.45  ipcrm: permission denied for id (799637562)
% 0.21/0.45  ipcrm: permission denied for id (801898555)
% 0.21/0.45  ipcrm: permission denied for id (801931324)
% 0.21/0.45  ipcrm: permission denied for id (799670333)
% 0.21/0.45  ipcrm: permission denied for id (799703102)
% 0.21/0.46  ipcrm: permission denied for id (804618303)
% 0.21/0.46  ipcrm: permission denied for id (799735872)
% 0.21/0.46  ipcrm: permission denied for id (801996865)
% 0.21/0.46  ipcrm: permission denied for id (804651074)
% 0.21/0.46  ipcrm: permission denied for id (802062403)
% 0.21/0.46  ipcrm: permission denied for id (802127941)
% 0.21/0.47  ipcrm: permission denied for id (802160710)
% 0.21/0.47  ipcrm: permission denied for id (802193479)
% 0.21/0.47  ipcrm: permission denied for id (802226248)
% 0.21/0.47  ipcrm: permission denied for id (804716617)
% 0.21/0.48  ipcrm: permission denied for id (802422861)
% 0.21/0.48  ipcrm: permission denied for id (802455630)
% 0.21/0.48  ipcrm: permission denied for id (802553937)
% 0.21/0.48  ipcrm: permission denied for id (799866962)
% 0.21/0.49  ipcrm: permission denied for id (802586707)
% 0.21/0.49  ipcrm: permission denied for id (802619476)
% 0.21/0.49  ipcrm: permission denied for id (802652245)
% 0.21/0.49  ipcrm: permission denied for id (802685014)
% 0.21/0.49  ipcrm: permission denied for id (802717783)
% 0.21/0.49  ipcrm: permission denied for id (802750552)
% 0.21/0.49  ipcrm: permission denied for id (802783321)
% 0.21/0.50  ipcrm: permission denied for id (804913242)
% 0.21/0.50  ipcrm: permission denied for id (799965275)
% 0.21/0.50  ipcrm: permission denied for id (802848860)
% 0.21/0.50  ipcrm: permission denied for id (804978782)
% 0.21/0.50  ipcrm: permission denied for id (800030815)
% 0.21/0.50  ipcrm: permission denied for id (802947168)
% 0.21/0.51  ipcrm: permission denied for id (800096354)
% 0.21/0.51  ipcrm: permission denied for id (803012707)
% 0.21/0.51  ipcrm: permission denied for id (803078244)
% 0.21/0.51  ipcrm: permission denied for id (803111013)
% 0.21/0.51  ipcrm: permission denied for id (803143782)
% 0.21/0.51  ipcrm: permission denied for id (805044327)
% 0.21/0.52  ipcrm: permission denied for id (803242089)
% 0.21/0.52  ipcrm: permission denied for id (803274858)
% 0.21/0.52  ipcrm: permission denied for id (800227435)
% 0.21/0.52  ipcrm: permission denied for id (803340397)
% 0.21/0.52  ipcrm: permission denied for id (803405935)
% 0.21/0.52  ipcrm: permission denied for id (803537010)
% 0.21/0.53  ipcrm: permission denied for id (803569779)
% 0.21/0.53  ipcrm: permission denied for id (805240948)
% 0.21/0.53  ipcrm: permission denied for id (803635317)
% 0.21/0.53  ipcrm: permission denied for id (803700855)
% 0.21/0.53  ipcrm: permission denied for id (805306488)
% 0.21/0.53  ipcrm: permission denied for id (803766393)
% 0.21/0.53  ipcrm: permission denied for id (803831931)
% 0.21/0.53  ipcrm: permission denied for id (803897469)
% 0.21/0.54  ipcrm: permission denied for id (800391294)
% 0.21/0.54  ipcrm: permission denied for id (803930239)
% 0.39/0.60  % (29948)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.39/0.64  % (29931)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.39/0.65  % (29944)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.39/0.65  % (29954)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.39/0.65  % (29946)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.39/0.65  % (29934)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.39/0.65  % (29945)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.39/0.65  % (29938)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.39/0.66  % (29942)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.39/0.66  % (29950)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.39/0.66  % (29932)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.39/0.66  % (29955)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.39/0.66  % (29953)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.39/0.66  % (29933)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.39/0.66  % (29937)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.39/0.66  % (29930)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.39/0.66  % (29951)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.39/0.66  % (29941)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.39/0.66  % (29939)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.39/0.67  % (29947)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.39/0.67  % (29943)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.39/0.67  % (29934)Refutation found. Thanks to Tanya!
% 0.39/0.67  % SZS status Theorem for theBenchmark
% 0.39/0.68  % (29940)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.39/0.68  % SZS output start Proof for theBenchmark
% 0.39/0.68  fof(f314,plain,(
% 0.39/0.68    $false),
% 0.39/0.68    inference(avatar_sat_refutation,[],[f141,f145,f206,f247,f301,f313])).
% 0.39/0.68  fof(f313,plain,(
% 0.39/0.68    spl3_10 | ~spl3_14),
% 0.39/0.68    inference(avatar_contradiction_clause,[],[f312])).
% 0.39/0.68  fof(f312,plain,(
% 0.39/0.68    $false | (spl3_10 | ~spl3_14)),
% 0.39/0.68    inference(subsumption_resolution,[],[f306,f303])).
% 0.39/0.68  fof(f303,plain,(
% 0.39/0.68    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_14),
% 0.39/0.68    inference(subsumption_resolution,[],[f302,f31])).
% 0.39/0.68  fof(f31,plain,(
% 0.39/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.39/0.68    inference(cnf_transformation,[],[f27])).
% 0.39/0.68  fof(f27,plain,(
% 0.39/0.68    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.39/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f26,f25,f24])).
% 0.39/0.68  fof(f24,plain,(
% 0.39/0.68    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.39/0.68    introduced(choice_axiom,[])).
% 0.39/0.68  fof(f25,plain,(
% 0.39/0.68    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.39/0.68    introduced(choice_axiom,[])).
% 0.39/0.68  fof(f26,plain,(
% 0.39/0.68    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.39/0.68    introduced(choice_axiom,[])).
% 0.39/0.68  fof(f12,plain,(
% 0.39/0.68    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.39/0.68    inference(ennf_transformation,[],[f11])).
% 0.39/0.68  fof(f11,negated_conjecture,(
% 0.39/0.68    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.39/0.68    inference(negated_conjecture,[],[f10])).
% 0.39/0.68  fof(f10,conjecture,(
% 0.39/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).
% 0.39/0.68  fof(f302,plain,(
% 0.39/0.68    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_14),
% 0.39/0.68    inference(subsumption_resolution,[],[f297,f32])).
% 0.39/0.68  fof(f32,plain,(
% 0.39/0.68    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.39/0.68    inference(cnf_transformation,[],[f27])).
% 0.39/0.68  fof(f297,plain,(
% 0.39/0.68    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_14),
% 0.39/0.68    inference(superposition,[],[f236,f44])).
% 0.39/0.68  fof(f44,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.39/0.68    inference(cnf_transformation,[],[f23])).
% 0.39/0.68  fof(f23,plain,(
% 0.39/0.68    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.39/0.68    inference(flattening,[],[f22])).
% 0.39/0.68  fof(f22,plain,(
% 0.39/0.68    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.39/0.68    inference(ennf_transformation,[],[f7])).
% 0.39/0.68  fof(f7,axiom,(
% 0.39/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.39/0.68  fof(f236,plain,(
% 0.39/0.68    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_14),
% 0.39/0.68    inference(avatar_component_clause,[],[f235])).
% 0.39/0.68  fof(f235,plain,(
% 0.39/0.68    spl3_14 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.39/0.68  fof(f306,plain,(
% 0.39/0.68    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 0.39/0.68    inference(subsumption_resolution,[],[f305,f30])).
% 0.39/0.68  fof(f30,plain,(
% 0.39/0.68    l1_pre_topc(sK0)),
% 0.39/0.68    inference(cnf_transformation,[],[f27])).
% 0.39/0.68  fof(f305,plain,(
% 0.39/0.68    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_10),
% 0.39/0.68    inference(subsumption_resolution,[],[f304,f31])).
% 0.39/0.68  fof(f304,plain,(
% 0.39/0.68    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_10),
% 0.39/0.68    inference(subsumption_resolution,[],[f294,f35])).
% 0.39/0.68  fof(f35,plain,(
% 0.39/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.39/0.68    inference(cnf_transformation,[],[f4])).
% 0.39/0.68  fof(f4,axiom,(
% 0.39/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.39/0.68  fof(f294,plain,(
% 0.39/0.68    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_10),
% 0.39/0.68    inference(resolution,[],[f201,f34])).
% 0.39/0.68  fof(f34,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f14])).
% 0.39/0.68  fof(f14,plain,(
% 0.39/0.68    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.39/0.68    inference(flattening,[],[f13])).
% 0.39/0.68  fof(f13,plain,(
% 0.39/0.68    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.39/0.68    inference(ennf_transformation,[],[f9])).
% 0.39/0.68  fof(f9,axiom,(
% 0.39/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 0.39/0.68  fof(f201,plain,(
% 0.39/0.68    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_10),
% 0.39/0.68    inference(avatar_component_clause,[],[f199])).
% 0.39/0.68  fof(f199,plain,(
% 0.39/0.68    spl3_10 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 0.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.39/0.68  fof(f301,plain,(
% 0.39/0.68    spl3_11 | ~spl3_14),
% 0.39/0.68    inference(avatar_contradiction_clause,[],[f300])).
% 0.39/0.68  fof(f300,plain,(
% 0.39/0.68    $false | (spl3_11 | ~spl3_14)),
% 0.39/0.68    inference(subsumption_resolution,[],[f299,f31])).
% 0.39/0.68  fof(f299,plain,(
% 0.39/0.68    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_11 | ~spl3_14)),
% 0.39/0.68    inference(subsumption_resolution,[],[f298,f32])).
% 0.39/0.68  fof(f298,plain,(
% 0.39/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_11 | ~spl3_14)),
% 0.39/0.68    inference(subsumption_resolution,[],[f297,f227])).
% 0.39/0.68  fof(f227,plain,(
% 0.39/0.68    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 0.39/0.68    inference(subsumption_resolution,[],[f226,f30])).
% 0.39/0.68  fof(f226,plain,(
% 0.39/0.68    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_11),
% 0.39/0.68    inference(subsumption_resolution,[],[f225,f32])).
% 0.39/0.68  fof(f225,plain,(
% 0.39/0.68    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_11),
% 0.39/0.68    inference(subsumption_resolution,[],[f222,f74])).
% 0.39/0.68  fof(f74,plain,(
% 0.39/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.39/0.68    inference(resolution,[],[f51,f45])).
% 0.39/0.68  fof(f45,plain,(
% 0.39/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.39/0.68    inference(equality_resolution,[],[f39])).
% 0.39/0.68  fof(f39,plain,(
% 0.39/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.39/0.68    inference(cnf_transformation,[],[f29])).
% 0.39/0.68  fof(f29,plain,(
% 0.39/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.39/0.68    inference(flattening,[],[f28])).
% 0.39/0.68  fof(f28,plain,(
% 0.39/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.39/0.68    inference(nnf_transformation,[],[f1])).
% 0.39/0.68  fof(f1,axiom,(
% 0.39/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.39/0.68  fof(f51,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0)) | r1_tarski(X2,k2_xboole_0(X0,X1))) )),
% 0.39/0.68    inference(superposition,[],[f41,f36])).
% 0.39/0.68  fof(f36,plain,(
% 0.39/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f2])).
% 0.39/0.68  fof(f2,axiom,(
% 0.39/0.68    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.39/0.68  fof(f41,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f17])).
% 0.39/0.68  fof(f17,plain,(
% 0.39/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.39/0.68    inference(ennf_transformation,[],[f3])).
% 0.39/0.68  fof(f3,axiom,(
% 0.39/0.68    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.39/0.68  fof(f222,plain,(
% 0.39/0.68    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_11),
% 0.39/0.68    inference(resolution,[],[f205,f34])).
% 0.39/0.68  fof(f205,plain,(
% 0.39/0.68    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_11),
% 0.39/0.68    inference(avatar_component_clause,[],[f203])).
% 0.39/0.68  fof(f203,plain,(
% 0.39/0.68    spl3_11 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 0.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.39/0.68  fof(f247,plain,(
% 0.39/0.68    spl3_14),
% 0.39/0.68    inference(avatar_contradiction_clause,[],[f246])).
% 0.39/0.68  fof(f246,plain,(
% 0.39/0.68    $false | spl3_14),
% 0.39/0.68    inference(subsumption_resolution,[],[f245,f31])).
% 0.39/0.68  fof(f245,plain,(
% 0.39/0.68    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_14),
% 0.39/0.68    inference(subsumption_resolution,[],[f243,f32])).
% 0.39/0.68  fof(f243,plain,(
% 0.39/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_14),
% 0.39/0.68    inference(resolution,[],[f237,f43])).
% 0.39/0.68  fof(f43,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.39/0.68    inference(cnf_transformation,[],[f21])).
% 0.39/0.68  fof(f21,plain,(
% 0.39/0.68    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.39/0.68    inference(flattening,[],[f20])).
% 0.39/0.68  fof(f20,plain,(
% 0.39/0.68    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.39/0.68    inference(ennf_transformation,[],[f6])).
% 0.39/0.68  fof(f6,axiom,(
% 0.39/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.39/0.68  fof(f237,plain,(
% 0.39/0.68    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_14),
% 0.39/0.68    inference(avatar_component_clause,[],[f235])).
% 0.39/0.68  fof(f206,plain,(
% 0.39/0.68    ~spl3_10 | ~spl3_11 | ~spl3_1 | ~spl3_2),
% 0.39/0.68    inference(avatar_split_clause,[],[f193,f128,f124,f203,f199])).
% 0.39/0.68  fof(f124,plain,(
% 0.39/0.68    spl3_1 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.39/0.68  fof(f128,plain,(
% 0.39/0.68    spl3_2 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.39/0.68  fof(f193,plain,(
% 0.39/0.68    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_1 | ~spl3_2)),
% 0.39/0.68    inference(resolution,[],[f150,f42])).
% 0.39/0.68  fof(f42,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f19])).
% 0.39/0.68  fof(f19,plain,(
% 0.39/0.68    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.39/0.68    inference(flattening,[],[f18])).
% 0.39/0.68  fof(f18,plain,(
% 0.39/0.68    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.39/0.68    inference(ennf_transformation,[],[f5])).
% 0.39/0.68  fof(f5,axiom,(
% 0.39/0.68    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.39/0.68  fof(f150,plain,(
% 0.39/0.68    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_1 | ~spl3_2)),
% 0.39/0.68    inference(subsumption_resolution,[],[f149,f125])).
% 0.39/0.68  fof(f125,plain,(
% 0.39/0.68    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_1),
% 0.39/0.68    inference(avatar_component_clause,[],[f124])).
% 0.39/0.68  fof(f149,plain,(
% 0.39/0.68    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.39/0.68    inference(subsumption_resolution,[],[f146,f129])).
% 0.39/0.68  fof(f129,plain,(
% 0.39/0.68    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.39/0.68    inference(avatar_component_clause,[],[f128])).
% 0.39/0.68  fof(f146,plain,(
% 0.39/0.68    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.39/0.68    inference(superposition,[],[f137,f44])).
% 0.39/0.68  fof(f137,plain,(
% 0.39/0.68    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 0.39/0.68    inference(subsumption_resolution,[],[f136,f31])).
% 0.39/0.68  fof(f136,plain,(
% 0.39/0.68    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.39/0.68    inference(subsumption_resolution,[],[f120,f32])).
% 0.39/0.68  fof(f120,plain,(
% 0.39/0.68    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.39/0.68    inference(superposition,[],[f33,f44])).
% 0.39/0.68  fof(f33,plain,(
% 0.39/0.68    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.39/0.68    inference(cnf_transformation,[],[f27])).
% 0.39/0.68  fof(f145,plain,(
% 0.39/0.68    spl3_2),
% 0.39/0.68    inference(avatar_contradiction_clause,[],[f144])).
% 0.39/0.68  fof(f144,plain,(
% 0.39/0.68    $false | spl3_2),
% 0.39/0.68    inference(subsumption_resolution,[],[f143,f30])).
% 0.39/0.68  fof(f143,plain,(
% 0.39/0.68    ~l1_pre_topc(sK0) | spl3_2),
% 0.39/0.68    inference(subsumption_resolution,[],[f142,f32])).
% 0.39/0.68  fof(f142,plain,(
% 0.39/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_2),
% 0.39/0.68    inference(resolution,[],[f130,f37])).
% 0.39/0.68  fof(f37,plain,(
% 0.39/0.68    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f16])).
% 0.39/0.68  fof(f16,plain,(
% 0.39/0.68    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.39/0.68    inference(flattening,[],[f15])).
% 0.39/0.68  fof(f15,plain,(
% 0.39/0.68    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.39/0.68    inference(ennf_transformation,[],[f8])).
% 0.39/0.68  fof(f8,axiom,(
% 0.39/0.68    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.39/0.68  fof(f130,plain,(
% 0.39/0.68    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 0.39/0.68    inference(avatar_component_clause,[],[f128])).
% 0.39/0.68  fof(f141,plain,(
% 0.39/0.68    spl3_1),
% 0.39/0.68    inference(avatar_contradiction_clause,[],[f140])).
% 0.39/0.68  fof(f140,plain,(
% 0.39/0.68    $false | spl3_1),
% 0.39/0.68    inference(subsumption_resolution,[],[f139,f30])).
% 0.39/0.68  fof(f139,plain,(
% 0.39/0.68    ~l1_pre_topc(sK0) | spl3_1),
% 0.39/0.68    inference(subsumption_resolution,[],[f138,f31])).
% 0.39/0.68  fof(f138,plain,(
% 0.39/0.68    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_1),
% 0.39/0.68    inference(resolution,[],[f126,f37])).
% 0.39/0.68  fof(f126,plain,(
% 0.39/0.68    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 0.39/0.68    inference(avatar_component_clause,[],[f124])).
% 0.39/0.68  % SZS output end Proof for theBenchmark
% 0.39/0.68  % (29934)------------------------------
% 0.39/0.68  % (29934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.68  % (29934)Termination reason: Refutation
% 0.39/0.68  
% 0.39/0.68  % (29934)Memory used [KB]: 6268
% 0.39/0.68  % (29934)Time elapsed: 0.094 s
% 0.39/0.68  % (29934)------------------------------
% 0.39/0.68  % (29934)------------------------------
% 0.39/0.68  % (29952)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.39/0.68  % (29935)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.39/0.68  % (29759)Success in time 0.319 s
%------------------------------------------------------------------------------
