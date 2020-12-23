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
% DateTime   : Thu Dec  3 13:11:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 327 expanded)
%              Number of leaves         :   22 ( 121 expanded)
%              Depth                    :   13
%              Number of atoms          :  303 (1123 expanded)
%              Number of equality atoms :   15 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f964,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f221,f234,f279,f342,f589,f603,f834,f963])).

fof(f963,plain,(
    spl3_26 ),
    inference(avatar_contradiction_clause,[],[f962])).

fof(f962,plain,
    ( $false
    | spl3_26 ),
    inference(subsumption_resolution,[],[f931,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f931,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl3_26 ),
    inference(resolution,[],[f572,f610])).

fof(f610,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK2,X0) )
    | spl3_26 ),
    inference(resolution,[],[f607,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f47,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f607,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | spl3_26 ),
    inference(subsumption_resolution,[],[f606,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(f606,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_26 ),
    inference(subsumption_resolution,[],[f605,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f605,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_26 ),
    inference(superposition,[],[f588,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f588,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f586])).

fof(f586,plain,
    ( spl3_26
  <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f572,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f112,f50])).

fof(f112,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k4_xboole_0(X5,X3),k4_xboole_0(X4,X3))
      | r1_tarski(X5,k2_xboole_0(X3,X4)) ) ),
    inference(superposition,[],[f46,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f834,plain,
    ( spl3_20
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f833])).

fof(f833,plain,
    ( $false
    | spl3_20
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f832,f33])).

fof(f832,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f831,f34])).

fof(f831,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f830,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f830,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20
    | ~ spl3_25 ),
    inference(superposition,[],[f826,f49])).

fof(f826,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_20
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f825,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f825,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | spl3_20
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f824,f33])).

fof(f824,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_20
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f821,f583])).

fof(f583,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f582])).

fof(f582,plain,
    ( spl3_25
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f821,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_20 ),
    inference(resolution,[],[f337,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f337,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl3_20
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f603,plain,(
    spl3_25 ),
    inference(avatar_contradiction_clause,[],[f602])).

fof(f602,plain,
    ( $false
    | spl3_25 ),
    inference(subsumption_resolution,[],[f601,f52])).

fof(f52,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f44,f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f601,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_25 ),
    inference(subsumption_resolution,[],[f598,f53])).

fof(f53,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f44,f34])).

fof(f598,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_25 ),
    inference(resolution,[],[f596,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f596,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_25 ),
    inference(resolution,[],[f595,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f595,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_25 ),
    inference(subsumption_resolution,[],[f594,f33])).

fof(f594,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_25 ),
    inference(subsumption_resolution,[],[f593,f34])).

fof(f593,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_25 ),
    inference(superposition,[],[f584,f49])).

fof(f584,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f582])).

fof(f589,plain,
    ( ~ spl3_25
    | ~ spl3_26
    | spl3_21 ),
    inference(avatar_split_clause,[],[f580,f339,f586,f582])).

fof(f339,plain,
    ( spl3_21
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f580,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_21 ),
    inference(subsumption_resolution,[],[f579,f32])).

fof(f579,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_21 ),
    inference(subsumption_resolution,[],[f576,f34])).

fof(f576,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_21 ),
    inference(resolution,[],[f341,f37])).

fof(f341,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f339])).

fof(f342,plain,
    ( ~ spl3_20
    | ~ spl3_21
    | spl3_11 ),
    inference(avatar_split_clause,[],[f330,f218,f339,f335])).

fof(f218,plain,
    ( spl3_11
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f330,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_11 ),
    inference(resolution,[],[f220,f48])).

fof(f220,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f218])).

fof(f279,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f270,f53])).

fof(f270,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f257,f178])).

fof(f178,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f175,f32])).

fof(f175,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f36,f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f257,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_10 ),
    inference(resolution,[],[f256,f58])).

fof(f256,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f216,f45])).

fof(f216,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl3_10
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f234,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f226,f52])).

fof(f226,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f225,f177])).

fof(f177,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f174,f32])).

fof(f174,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f36,f33])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_9 ),
    inference(resolution,[],[f224,f58])).

fof(f224,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f212,f45])).

fof(f212,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl3_9
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f221,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f207,f218,f214,f210])).

fof(f207,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f35,f49])).

fof(f35,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:19:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (14849)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (14841)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (14839)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (14844)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (14838)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (14851)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (14848)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (14847)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (14836)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (14858)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (14855)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (14853)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (14850)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (14835)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (14837)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (14856)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (14843)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (14861)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (14852)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (14840)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (14854)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (14859)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (14846)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (14857)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (14860)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (14845)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.57  % (14839)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f964,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f221,f234,f279,f342,f589,f603,f834,f963])).
% 0.21/0.57  fof(f963,plain,(
% 0.21/0.57    spl3_26),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f962])).
% 0.21/0.57  fof(f962,plain,(
% 0.21/0.57    $false | spl3_26),
% 0.21/0.57    inference(subsumption_resolution,[],[f931,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f931,plain,(
% 0.21/0.57    ~r1_tarski(sK2,sK2) | spl3_26),
% 0.21/0.57    inference(resolution,[],[f572,f610])).
% 0.21/0.57  fof(f610,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK2,X0)) ) | spl3_26),
% 0.21/0.57    inference(resolution,[],[f607,f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(superposition,[],[f47,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.57  fof(f607,plain,(
% 0.21/0.57    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | spl3_26),
% 0.21/0.57    inference(subsumption_resolution,[],[f606,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27,f26,f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.21/0.57    inference(negated_conjecture,[],[f12])).
% 0.21/0.57  fof(f12,conjecture,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).
% 0.21/0.57  fof(f606,plain,(
% 0.21/0.57    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_26),
% 0.21/0.57    inference(subsumption_resolution,[],[f605,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f605,plain,(
% 0.21/0.57    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_26),
% 0.21/0.57    inference(superposition,[],[f588,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(flattening,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.57  fof(f588,plain,(
% 0.21/0.57    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl3_26),
% 0.21/0.57    inference(avatar_component_clause,[],[f586])).
% 0.21/0.57  fof(f586,plain,(
% 0.21/0.57    spl3_26 <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.57  fof(f572,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.57    inference(resolution,[],[f112,f50])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (~r1_tarski(k4_xboole_0(X5,X3),k4_xboole_0(X4,X3)) | r1_tarski(X5,k2_xboole_0(X3,X4))) )),
% 0.21/0.57    inference(superposition,[],[f46,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.21/0.57  fof(f834,plain,(
% 0.21/0.57    spl3_20 | ~spl3_25),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f833])).
% 0.21/0.57  fof(f833,plain,(
% 0.21/0.57    $false | (spl3_20 | ~spl3_25)),
% 0.21/0.57    inference(subsumption_resolution,[],[f832,f33])).
% 0.21/0.57  fof(f832,plain,(
% 0.21/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_20 | ~spl3_25)),
% 0.21/0.57    inference(subsumption_resolution,[],[f831,f34])).
% 0.21/0.57  fof(f831,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_20 | ~spl3_25)),
% 0.21/0.57    inference(subsumption_resolution,[],[f830,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.57  fof(f830,plain,(
% 0.21/0.57    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_20 | ~spl3_25)),
% 0.21/0.57    inference(superposition,[],[f826,f49])).
% 0.21/0.57  fof(f826,plain,(
% 0.21/0.57    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | (spl3_20 | ~spl3_25)),
% 0.21/0.57    inference(subsumption_resolution,[],[f825,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    l1_pre_topc(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f825,plain,(
% 0.21/0.57    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~l1_pre_topc(sK0) | (spl3_20 | ~spl3_25)),
% 0.21/0.57    inference(subsumption_resolution,[],[f824,f33])).
% 0.21/0.57  fof(f824,plain,(
% 0.21/0.57    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_20 | ~spl3_25)),
% 0.21/0.57    inference(subsumption_resolution,[],[f821,f583])).
% 0.21/0.57  fof(f583,plain,(
% 0.21/0.57    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_25),
% 0.21/0.57    inference(avatar_component_clause,[],[f582])).
% 0.21/0.57  fof(f582,plain,(
% 0.21/0.57    spl3_25 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.57  fof(f821,plain,(
% 0.21/0.57    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_20),
% 0.21/0.57    inference(resolution,[],[f337,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.21/0.57  fof(f337,plain,(
% 0.21/0.57    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_20),
% 0.21/0.57    inference(avatar_component_clause,[],[f335])).
% 0.21/0.57  fof(f335,plain,(
% 0.21/0.57    spl3_20 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.57  fof(f603,plain,(
% 0.21/0.57    spl3_25),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f602])).
% 0.21/0.57  fof(f602,plain,(
% 0.21/0.57    $false | spl3_25),
% 0.21/0.57    inference(subsumption_resolution,[],[f601,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.57    inference(resolution,[],[f44,f33])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.57  fof(f601,plain,(
% 0.21/0.57    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_25),
% 0.21/0.57    inference(subsumption_resolution,[],[f598,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.21/0.57    inference(resolution,[],[f44,f34])).
% 0.21/0.57  fof(f598,plain,(
% 0.21/0.57    ~r1_tarski(sK2,u1_struct_0(sK0)) | ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_25),
% 0.21/0.57    inference(resolution,[],[f596,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.57  fof(f596,plain,(
% 0.21/0.57    ~r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_25),
% 0.21/0.57    inference(resolution,[],[f595,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f595,plain,(
% 0.21/0.57    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_25),
% 0.21/0.57    inference(subsumption_resolution,[],[f594,f33])).
% 0.21/0.57  fof(f594,plain,(
% 0.21/0.57    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_25),
% 0.21/0.57    inference(subsumption_resolution,[],[f593,f34])).
% 0.21/0.57  fof(f593,plain,(
% 0.21/0.57    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_25),
% 0.21/0.57    inference(superposition,[],[f584,f49])).
% 0.21/0.57  fof(f584,plain,(
% 0.21/0.57    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_25),
% 0.21/0.57    inference(avatar_component_clause,[],[f582])).
% 0.21/0.57  fof(f589,plain,(
% 0.21/0.57    ~spl3_25 | ~spl3_26 | spl3_21),
% 0.21/0.57    inference(avatar_split_clause,[],[f580,f339,f586,f582])).
% 0.21/0.57  fof(f339,plain,(
% 0.21/0.57    spl3_21 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.57  fof(f580,plain,(
% 0.21/0.57    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_21),
% 0.21/0.57    inference(subsumption_resolution,[],[f579,f32])).
% 0.21/0.57  fof(f579,plain,(
% 0.21/0.57    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_21),
% 0.21/0.57    inference(subsumption_resolution,[],[f576,f34])).
% 0.21/0.57  fof(f576,plain,(
% 0.21/0.57    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_21),
% 0.21/0.57    inference(resolution,[],[f341,f37])).
% 0.21/0.57  fof(f341,plain,(
% 0.21/0.57    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_21),
% 0.21/0.57    inference(avatar_component_clause,[],[f339])).
% 0.21/0.57  fof(f342,plain,(
% 0.21/0.57    ~spl3_20 | ~spl3_21 | spl3_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f330,f218,f339,f335])).
% 0.21/0.57  fof(f218,plain,(
% 0.21/0.57    spl3_11 <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.57  fof(f330,plain,(
% 0.21/0.57    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_11),
% 0.21/0.57    inference(resolution,[],[f220,f48])).
% 0.21/0.57  fof(f220,plain,(
% 0.21/0.57    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f218])).
% 0.21/0.57  fof(f279,plain,(
% 0.21/0.57    spl3_10),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f278])).
% 0.21/0.57  fof(f278,plain,(
% 0.21/0.57    $false | spl3_10),
% 0.21/0.57    inference(subsumption_resolution,[],[f270,f53])).
% 0.21/0.57  fof(f270,plain,(
% 0.21/0.57    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_10),
% 0.21/0.57    inference(resolution,[],[f257,f178])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f175,f32])).
% 0.21/0.57  fof(f175,plain,(
% 0.21/0.57    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.57    inference(resolution,[],[f36,f34])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.57  fof(f257,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_10),
% 0.21/0.57    inference(resolution,[],[f256,f58])).
% 0.21/0.57  fof(f256,plain,(
% 0.21/0.57    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_10),
% 0.21/0.57    inference(resolution,[],[f216,f45])).
% 0.21/0.57  fof(f216,plain,(
% 0.21/0.57    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f214])).
% 0.21/0.57  fof(f214,plain,(
% 0.21/0.57    spl3_10 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.57  fof(f234,plain,(
% 0.21/0.57    spl3_9),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.57  fof(f233,plain,(
% 0.21/0.57    $false | spl3_9),
% 0.21/0.57    inference(subsumption_resolution,[],[f226,f52])).
% 0.21/0.57  fof(f226,plain,(
% 0.21/0.57    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_9),
% 0.21/0.57    inference(resolution,[],[f225,f177])).
% 0.21/0.57  fof(f177,plain,(
% 0.21/0.57    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f174,f32])).
% 0.21/0.57  fof(f174,plain,(
% 0.21/0.57    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.57    inference(resolution,[],[f36,f33])).
% 0.21/0.57  fof(f225,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_9),
% 0.21/0.57    inference(resolution,[],[f224,f58])).
% 0.21/0.57  fof(f224,plain,(
% 0.21/0.57    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_9),
% 0.21/0.57    inference(resolution,[],[f212,f45])).
% 0.21/0.57  fof(f212,plain,(
% 0.21/0.57    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f210])).
% 0.21/0.57  fof(f210,plain,(
% 0.21/0.57    spl3_9 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.57  fof(f221,plain,(
% 0.21/0.57    ~spl3_9 | ~spl3_10 | ~spl3_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f207,f218,f214,f210])).
% 0.21/0.57  fof(f207,plain,(
% 0.21/0.57    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    inference(superposition,[],[f35,f49])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (14839)------------------------------
% 0.21/0.57  % (14839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14839)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (14839)Memory used [KB]: 6524
% 0.21/0.57  % (14839)Time elapsed: 0.154 s
% 0.21/0.57  % (14839)------------------------------
% 0.21/0.57  % (14839)------------------------------
% 0.21/0.57  % (14832)Success in time 0.213 s
%------------------------------------------------------------------------------
