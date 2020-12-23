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
% DateTime   : Thu Dec  3 13:10:52 EST 2020

% Result     : Theorem 2.63s
% Output     : Refutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 335 expanded)
%              Number of leaves         :   24 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          :  345 (1247 expanded)
%              Number of equality atoms :   35 (  66 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f112,f264,f280,f3305,f3316,f3388])).

fof(f3388,plain,
    ( ~ spl3_16
    | spl3_37 ),
    inference(avatar_contradiction_clause,[],[f3387])).

fof(f3387,plain,
    ( $false
    | ~ spl3_16
    | spl3_37 ),
    inference(subsumption_resolution,[],[f3386,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f3386,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl3_16
    | spl3_37 ),
    inference(subsumption_resolution,[],[f3385,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).

fof(f3385,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl3_16
    | spl3_37 ),
    inference(subsumption_resolution,[],[f3383,f3327])).

fof(f3327,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f3317,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3317,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_16 ),
    inference(resolution,[],[f274,f178])).

fof(f178,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k4_xboole_0(X3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_xboole_0(sK2,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f153,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f153,plain,(
    ! [X0] :
      ( m1_subset_1(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f150,f58])).

fof(f150,plain,(
    ! [X0] :
      ( m1_subset_1(k2_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f149,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f149,plain,(
    ! [X0] :
      ( m1_subset_1(k2_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X0] :
      ( m1_subset_1(k2_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f82,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f274,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl3_16
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f3383,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | spl3_37 ),
    inference(resolution,[],[f3304,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f3304,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f3302])).

fof(f3302,plain,
    ( spl3_37
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f3316,plain,
    ( ~ spl3_14
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f3315])).

fof(f3315,plain,
    ( $false
    | ~ spl3_14
    | spl3_16 ),
    inference(subsumption_resolution,[],[f3314,f71])).

fof(f71,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f43,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f3314,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_14
    | spl3_16 ),
    inference(forward_demodulation,[],[f3313,f263])).

fof(f263,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl3_14
  <=> u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f3313,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK2,u1_struct_0(sK0)))
    | spl3_16 ),
    inference(resolution,[],[f3312,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f3312,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_16 ),
    inference(resolution,[],[f275,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f275,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f273])).

fof(f3305,plain,
    ( ~ spl3_16
    | ~ spl3_37
    | spl3_6 ),
    inference(avatar_split_clause,[],[f3300,f104,f3302,f273])).

fof(f104,plain,
    ( spl3_6
  <=> r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f3300,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6 ),
    inference(forward_demodulation,[],[f3299,f58])).

fof(f3299,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6 ),
    inference(forward_demodulation,[],[f3298,f60])).

fof(f3298,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6 ),
    inference(subsumption_resolution,[],[f3277,f44])).

fof(f3277,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6 ),
    inference(superposition,[],[f239,f815])).

fof(f815,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,X3)) = k2_pre_topc(sK0,k2_xboole_0(X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f807])).

fof(f807,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,X3)) = k2_pre_topc(sK0,k2_xboole_0(X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f309,f62])).

fof(f309,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,X3)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f308,f69])).

fof(f69,plain,(
    ! [X2] :
      ( m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f42,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f308,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,X3)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f306,f69])).

fof(f306,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,X3)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k2_pre_topc(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f67,f62])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f66,f42])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f41,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f239,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))))
    | spl3_6 ),
    inference(resolution,[],[f188,f59])).

fof(f188,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_6 ),
    inference(subsumption_resolution,[],[f187,f43])).

fof(f187,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6 ),
    inference(superposition,[],[f106,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f106,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f280,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl3_13 ),
    inference(subsumption_resolution,[],[f278,f83])).

fof(f83,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f44,f47])).

fof(f278,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_13 ),
    inference(subsumption_resolution,[],[f277,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f277,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_13 ),
    inference(superposition,[],[f259,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f259,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k2_xboole_0(sK2,u1_struct_0(sK0)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl3_13
  <=> r1_tarski(u1_struct_0(sK0),k2_xboole_0(sK2,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f264,plain,
    ( ~ spl3_13
    | spl3_14 ),
    inference(avatar_split_clause,[],[f254,f261,f257])).

fof(f254,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(u1_struct_0(sK0),k2_xboole_0(sK2,u1_struct_0(sK0))) ),
    inference(resolution,[],[f252,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f252,plain,(
    r1_tarski(k2_xboole_0(sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f250,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f250,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(X0,sK2),u1_struct_0(sK0))
      | r1_tarski(k2_xboole_0(sK2,X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f166,f48])).

fof(f166,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k4_xboole_0(X3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_xboole_0(sK2,X3),u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f158,f60])).

fof(f158,plain,(
    ! [X0] :
      ( r1_tarski(k2_xboole_0(sK2,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f152,f58])).

fof(f152,plain,(
    ! [X2] :
      ( r1_tarski(k2_xboole_0(X2,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f150,f47])).

fof(f112,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f109,f43])).

fof(f109,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(resolution,[],[f102,f69])).

fof(f102,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_5
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f107,plain,
    ( ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f97,f104,f100])).

fof(f97,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f45,f54])).

fof(f45,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:15:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (24211)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.48  % (24218)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.49  % (24222)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.49  % (24212)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (24221)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (24223)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (24214)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (24219)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (24209)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (24201)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (24226)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (24206)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (24202)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (24215)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (24203)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (24207)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (24204)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (24216)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (24225)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (24205)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (24217)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (24213)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.32/0.52  % (24208)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.32/0.53  % (24220)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.32/0.54  % (24224)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.45/0.54  % (24210)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 2.11/0.66  % (24210)Refutation not found, incomplete strategy% (24210)------------------------------
% 2.11/0.66  % (24210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.66  % (24210)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.66  
% 2.11/0.66  % (24210)Memory used [KB]: 6268
% 2.11/0.66  % (24210)Time elapsed: 0.250 s
% 2.11/0.66  % (24210)------------------------------
% 2.11/0.66  % (24210)------------------------------
% 2.63/0.72  % (24207)Refutation found. Thanks to Tanya!
% 2.63/0.72  % SZS status Theorem for theBenchmark
% 2.63/0.72  % SZS output start Proof for theBenchmark
% 2.63/0.72  fof(f3398,plain,(
% 2.63/0.72    $false),
% 2.63/0.72    inference(avatar_sat_refutation,[],[f107,f112,f264,f280,f3305,f3316,f3388])).
% 2.63/0.72  fof(f3388,plain,(
% 2.63/0.72    ~spl3_16 | spl3_37),
% 2.63/0.72    inference(avatar_contradiction_clause,[],[f3387])).
% 2.63/0.72  fof(f3387,plain,(
% 2.63/0.72    $false | (~spl3_16 | spl3_37)),
% 2.63/0.72    inference(subsumption_resolution,[],[f3386,f53])).
% 2.63/0.72  fof(f53,plain,(
% 2.63/0.72    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.63/0.72    inference(cnf_transformation,[],[f8])).
% 2.63/0.72  fof(f8,axiom,(
% 2.63/0.72    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.63/0.72  fof(f3386,plain,(
% 2.63/0.72    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | (~spl3_16 | spl3_37)),
% 2.63/0.72    inference(subsumption_resolution,[],[f3385,f43])).
% 2.63/0.72  fof(f43,plain,(
% 2.63/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.63/0.72    inference(cnf_transformation,[],[f37])).
% 2.63/0.72  fof(f37,plain,(
% 2.63/0.72    ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.63/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f36,f35,f34])).
% 2.63/0.72  fof(f34,plain,(
% 2.63/0.72    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.63/0.72    introduced(choice_axiom,[])).
% 2.63/0.72  fof(f35,plain,(
% 2.63/0.72    ? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.63/0.72    introduced(choice_axiom,[])).
% 2.63/0.72  fof(f36,plain,(
% 2.63/0.72    ? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.63/0.72    introduced(choice_axiom,[])).
% 2.63/0.72  fof(f19,plain,(
% 2.63/0.72    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.63/0.72    inference(flattening,[],[f18])).
% 2.63/0.72  fof(f18,plain,(
% 2.63/0.72    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.63/0.72    inference(ennf_transformation,[],[f17])).
% 2.63/0.72  fof(f17,negated_conjecture,(
% 2.63/0.72    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 2.63/0.72    inference(negated_conjecture,[],[f16])).
% 2.63/0.72  fof(f16,conjecture,(
% 2.63/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).
% 2.63/0.72  fof(f3385,plain,(
% 2.63/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | (~spl3_16 | spl3_37)),
% 2.63/0.72    inference(subsumption_resolution,[],[f3383,f3327])).
% 2.63/0.72  fof(f3327,plain,(
% 2.63/0.72    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_16),
% 2.63/0.72    inference(forward_demodulation,[],[f3317,f58])).
% 2.63/0.72  fof(f58,plain,(
% 2.63/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.63/0.72    inference(cnf_transformation,[],[f1])).
% 2.63/0.72  fof(f1,axiom,(
% 2.63/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.63/0.72  fof(f3317,plain,(
% 2.63/0.72    m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_16),
% 2.63/0.72    inference(resolution,[],[f274,f178])).
% 2.63/0.72  fof(f178,plain,(
% 2.63/0.72    ( ! [X3] : (~m1_subset_1(k4_xboole_0(X3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_xboole_0(sK2,X3),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(superposition,[],[f153,f60])).
% 2.63/0.72  fof(f60,plain,(
% 2.63/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.63/0.72    inference(cnf_transformation,[],[f6])).
% 2.63/0.72  fof(f6,axiom,(
% 2.63/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.63/0.72  fof(f153,plain,(
% 2.63/0.72    ( ! [X0] : (m1_subset_1(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(superposition,[],[f150,f58])).
% 2.63/0.72  fof(f150,plain,(
% 2.63/0.72    ( ! [X0] : (m1_subset_1(k2_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(subsumption_resolution,[],[f149,f44])).
% 2.63/0.72  fof(f44,plain,(
% 2.63/0.72    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.63/0.72    inference(cnf_transformation,[],[f37])).
% 2.63/0.72  fof(f149,plain,(
% 2.63/0.72    ( ! [X0] : (m1_subset_1(k2_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(duplicate_literal_removal,[],[f148])).
% 2.63/0.72  fof(f148,plain,(
% 2.63/0.72    ( ! [X0] : (m1_subset_1(k2_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(superposition,[],[f82,f62])).
% 2.63/0.72  fof(f62,plain,(
% 2.63/0.72    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.63/0.72    inference(cnf_transformation,[],[f31])).
% 2.63/0.72  fof(f31,plain,(
% 2.63/0.72    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.63/0.72    inference(flattening,[],[f30])).
% 2.63/0.72  fof(f30,plain,(
% 2.63/0.72    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.63/0.72    inference(ennf_transformation,[],[f10])).
% 2.63/0.72  fof(f10,axiom,(
% 2.63/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.63/0.72  fof(f82,plain,(
% 2.63/0.72    ( ! [X0] : (m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(resolution,[],[f44,f63])).
% 2.63/0.72  fof(f63,plain,(
% 2.63/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.63/0.72    inference(cnf_transformation,[],[f33])).
% 2.63/0.72  fof(f33,plain,(
% 2.63/0.72    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.63/0.72    inference(flattening,[],[f32])).
% 2.63/0.72  fof(f32,plain,(
% 2.63/0.72    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.63/0.72    inference(ennf_transformation,[],[f9])).
% 2.63/0.72  fof(f9,axiom,(
% 2.63/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.63/0.72  fof(f274,plain,(
% 2.63/0.72    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_16),
% 2.63/0.72    inference(avatar_component_clause,[],[f273])).
% 2.63/0.72  fof(f273,plain,(
% 2.63/0.72    spl3_16 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.63/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.63/0.72  fof(f3383,plain,(
% 2.63/0.72    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | spl3_37),
% 2.63/0.72    inference(resolution,[],[f3304,f68])).
% 2.63/0.72  fof(f68,plain,(
% 2.63/0.72    ( ! [X0,X1] : (r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1)) )),
% 2.63/0.72    inference(resolution,[],[f42,f56])).
% 2.63/0.72  fof(f56,plain,(
% 2.63/0.72    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 2.63/0.72    inference(cnf_transformation,[],[f26])).
% 2.63/0.72  fof(f26,plain,(
% 2.63/0.72    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.72    inference(flattening,[],[f25])).
% 2.63/0.72  fof(f25,plain,(
% 2.63/0.72    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.72    inference(ennf_transformation,[],[f14])).
% 2.63/0.72  fof(f14,axiom,(
% 2.63/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).
% 2.63/0.72  fof(f42,plain,(
% 2.63/0.72    l1_pre_topc(sK0)),
% 2.63/0.72    inference(cnf_transformation,[],[f37])).
% 2.63/0.72  fof(f3304,plain,(
% 2.63/0.72    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) | spl3_37),
% 2.63/0.72    inference(avatar_component_clause,[],[f3302])).
% 2.63/0.72  fof(f3302,plain,(
% 2.63/0.72    spl3_37 <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 2.63/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 2.63/0.72  fof(f3316,plain,(
% 2.63/0.72    ~spl3_14 | spl3_16),
% 2.63/0.72    inference(avatar_contradiction_clause,[],[f3315])).
% 2.63/0.72  fof(f3315,plain,(
% 2.63/0.72    $false | (~spl3_14 | spl3_16)),
% 2.63/0.72    inference(subsumption_resolution,[],[f3314,f71])).
% 2.63/0.72  fof(f71,plain,(
% 2.63/0.72    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.63/0.72    inference(resolution,[],[f43,f47])).
% 2.63/0.72  fof(f47,plain,(
% 2.63/0.72    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.63/0.72    inference(cnf_transformation,[],[f38])).
% 2.63/0.72  fof(f38,plain,(
% 2.63/0.72    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.63/0.72    inference(nnf_transformation,[],[f12])).
% 2.63/0.72  fof(f12,axiom,(
% 2.63/0.72    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.63/0.72  fof(f3314,plain,(
% 2.63/0.72    ~r1_tarski(sK1,u1_struct_0(sK0)) | (~spl3_14 | spl3_16)),
% 2.63/0.72    inference(forward_demodulation,[],[f3313,f263])).
% 2.63/0.72  fof(f263,plain,(
% 2.63/0.72    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) | ~spl3_14),
% 2.63/0.72    inference(avatar_component_clause,[],[f261])).
% 2.63/0.72  fof(f261,plain,(
% 2.63/0.72    spl3_14 <=> u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))),
% 2.63/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.63/0.72  fof(f3313,plain,(
% 2.63/0.72    ~r1_tarski(sK1,k2_xboole_0(sK2,u1_struct_0(sK0))) | spl3_16),
% 2.63/0.72    inference(resolution,[],[f3312,f59])).
% 2.63/0.72  fof(f59,plain,(
% 2.63/0.72    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.63/0.72    inference(cnf_transformation,[],[f29])).
% 2.63/0.72  fof(f29,plain,(
% 2.63/0.72    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.63/0.72    inference(ennf_transformation,[],[f7])).
% 2.63/0.72  fof(f7,axiom,(
% 2.63/0.72    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.63/0.72  fof(f3312,plain,(
% 2.63/0.72    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_16),
% 2.63/0.72    inference(resolution,[],[f275,f48])).
% 2.63/0.72  fof(f48,plain,(
% 2.63/0.72    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.63/0.72    inference(cnf_transformation,[],[f38])).
% 2.63/0.72  fof(f275,plain,(
% 2.63/0.72    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_16),
% 2.63/0.72    inference(avatar_component_clause,[],[f273])).
% 2.63/0.72  fof(f3305,plain,(
% 2.63/0.72    ~spl3_16 | ~spl3_37 | spl3_6),
% 2.63/0.72    inference(avatar_split_clause,[],[f3300,f104,f3302,f273])).
% 2.63/0.72  fof(f104,plain,(
% 2.63/0.72    spl3_6 <=> r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 2.63/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.63/0.72  fof(f3300,plain,(
% 2.63/0.72    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_6),
% 2.63/0.72    inference(forward_demodulation,[],[f3299,f58])).
% 2.63/0.72  fof(f3299,plain,(
% 2.63/0.72    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_6),
% 2.63/0.72    inference(forward_demodulation,[],[f3298,f60])).
% 2.63/0.72  fof(f3298,plain,(
% 2.63/0.72    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_6),
% 2.63/0.72    inference(subsumption_resolution,[],[f3277,f44])).
% 2.63/0.72  fof(f3277,plain,(
% 2.63/0.72    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_6),
% 2.63/0.72    inference(superposition,[],[f239,f815])).
% 2.63/0.72  fof(f815,plain,(
% 2.63/0.72    ( ! [X2,X3] : (k2_xboole_0(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,X3)) = k2_pre_topc(sK0,k2_xboole_0(X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(duplicate_literal_removal,[],[f807])).
% 2.63/0.72  fof(f807,plain,(
% 2.63/0.72    ( ! [X2,X3] : (k2_xboole_0(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,X3)) = k2_pre_topc(sK0,k2_xboole_0(X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(superposition,[],[f309,f62])).
% 2.63/0.72  fof(f309,plain,(
% 2.63/0.72    ( ! [X2,X3] : (k2_xboole_0(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,X3)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(subsumption_resolution,[],[f308,f69])).
% 2.63/0.72  fof(f69,plain,(
% 2.63/0.72    ( ! [X2] : (m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(resolution,[],[f42,f55])).
% 2.63/0.72  fof(f55,plain,(
% 2.63/0.72    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.63/0.72    inference(cnf_transformation,[],[f24])).
% 2.63/0.72  fof(f24,plain,(
% 2.63/0.72    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.63/0.72    inference(flattening,[],[f23])).
% 2.63/0.72  fof(f23,plain,(
% 2.63/0.72    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.63/0.72    inference(ennf_transformation,[],[f13])).
% 2.63/0.72  fof(f13,axiom,(
% 2.63/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.63/0.72  fof(f308,plain,(
% 2.63/0.72    ( ! [X2,X3] : (k2_xboole_0(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,X3)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(subsumption_resolution,[],[f306,f69])).
% 2.63/0.72  fof(f306,plain,(
% 2.63/0.72    ( ! [X2,X3] : (k2_xboole_0(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,X3)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(superposition,[],[f67,f62])).
% 2.63/0.72  fof(f67,plain,(
% 2.63/0.72    ( ! [X0,X1] : (k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(subsumption_resolution,[],[f66,f42])).
% 2.63/0.72  fof(f66,plain,(
% 2.63/0.72    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))) )),
% 2.63/0.72    inference(resolution,[],[f41,f57])).
% 2.63/0.72  fof(f57,plain,(
% 2.63/0.72    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 2.63/0.72    inference(cnf_transformation,[],[f28])).
% 2.63/0.72  fof(f28,plain,(
% 2.63/0.72    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.63/0.72    inference(flattening,[],[f27])).
% 2.63/0.72  fof(f27,plain,(
% 2.63/0.72    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.63/0.72    inference(ennf_transformation,[],[f15])).
% 2.63/0.72  fof(f15,axiom,(
% 2.63/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).
% 2.63/0.72  fof(f41,plain,(
% 2.63/0.72    v2_pre_topc(sK0)),
% 2.63/0.72    inference(cnf_transformation,[],[f37])).
% 2.63/0.72  fof(f239,plain,(
% 2.63/0.72    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))) | spl3_6),
% 2.63/0.72    inference(resolution,[],[f188,f59])).
% 2.63/0.72  fof(f188,plain,(
% 2.63/0.72    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) | spl3_6),
% 2.63/0.72    inference(subsumption_resolution,[],[f187,f43])).
% 2.63/0.72  fof(f187,plain,(
% 2.63/0.72    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_6),
% 2.63/0.72    inference(superposition,[],[f106,f54])).
% 2.63/0.72  fof(f54,plain,(
% 2.63/0.72    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.63/0.72    inference(cnf_transformation,[],[f22])).
% 2.63/0.72  fof(f22,plain,(
% 2.63/0.72    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.63/0.72    inference(ennf_transformation,[],[f11])).
% 2.63/0.72  fof(f11,axiom,(
% 2.63/0.72    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.63/0.72  fof(f106,plain,(
% 2.63/0.72    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_6),
% 2.63/0.72    inference(avatar_component_clause,[],[f104])).
% 2.63/0.72  fof(f280,plain,(
% 2.63/0.72    spl3_13),
% 2.63/0.72    inference(avatar_contradiction_clause,[],[f279])).
% 2.63/0.72  fof(f279,plain,(
% 2.63/0.72    $false | spl3_13),
% 2.63/0.72    inference(subsumption_resolution,[],[f278,f83])).
% 2.63/0.72  fof(f83,plain,(
% 2.63/0.72    r1_tarski(sK2,u1_struct_0(sK0))),
% 2.63/0.72    inference(resolution,[],[f44,f47])).
% 2.63/0.72  fof(f278,plain,(
% 2.63/0.72    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_13),
% 2.63/0.72    inference(subsumption_resolution,[],[f277,f65])).
% 2.63/0.72  fof(f65,plain,(
% 2.63/0.72    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.63/0.72    inference(equality_resolution,[],[f49])).
% 2.63/0.72  fof(f49,plain,(
% 2.63/0.72    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.63/0.72    inference(cnf_transformation,[],[f40])).
% 2.63/0.72  fof(f40,plain,(
% 2.63/0.72    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.63/0.72    inference(flattening,[],[f39])).
% 2.63/0.72  fof(f39,plain,(
% 2.63/0.72    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.63/0.72    inference(nnf_transformation,[],[f2])).
% 2.63/0.72  fof(f2,axiom,(
% 2.63/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.63/0.72  fof(f277,plain,(
% 2.63/0.72    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_13),
% 2.63/0.72    inference(superposition,[],[f259,f52])).
% 2.63/0.72  fof(f52,plain,(
% 2.63/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.63/0.72    inference(cnf_transformation,[],[f21])).
% 2.63/0.72  fof(f21,plain,(
% 2.63/0.72    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.63/0.72    inference(ennf_transformation,[],[f4])).
% 2.63/0.72  fof(f4,axiom,(
% 2.63/0.72    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.63/0.72  fof(f259,plain,(
% 2.63/0.72    ~r1_tarski(u1_struct_0(sK0),k2_xboole_0(sK2,u1_struct_0(sK0))) | spl3_13),
% 2.63/0.72    inference(avatar_component_clause,[],[f257])).
% 2.63/0.72  fof(f257,plain,(
% 2.63/0.72    spl3_13 <=> r1_tarski(u1_struct_0(sK0),k2_xboole_0(sK2,u1_struct_0(sK0)))),
% 2.63/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.63/0.72  fof(f264,plain,(
% 2.63/0.72    ~spl3_13 | spl3_14),
% 2.63/0.72    inference(avatar_split_clause,[],[f254,f261,f257])).
% 2.63/0.72  fof(f254,plain,(
% 2.63/0.72    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) | ~r1_tarski(u1_struct_0(sK0),k2_xboole_0(sK2,u1_struct_0(sK0)))),
% 2.63/0.72    inference(resolution,[],[f252,f51])).
% 2.63/0.72  fof(f51,plain,(
% 2.63/0.72    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.63/0.72    inference(cnf_transformation,[],[f40])).
% 2.63/0.72  fof(f252,plain,(
% 2.63/0.72    r1_tarski(k2_xboole_0(sK2,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 2.63/0.72    inference(resolution,[],[f250,f61])).
% 2.63/0.72  fof(f61,plain,(
% 2.63/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.63/0.72    inference(cnf_transformation,[],[f5])).
% 2.63/0.72  fof(f5,axiom,(
% 2.63/0.72    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.63/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.63/0.72  fof(f250,plain,(
% 2.63/0.72    ( ! [X0] : (~r1_tarski(k4_xboole_0(X0,sK2),u1_struct_0(sK0)) | r1_tarski(k2_xboole_0(sK2,X0),u1_struct_0(sK0))) )),
% 2.63/0.72    inference(resolution,[],[f166,f48])).
% 2.63/0.72  fof(f166,plain,(
% 2.63/0.72    ( ! [X3] : (~m1_subset_1(k4_xboole_0(X3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_xboole_0(sK2,X3),u1_struct_0(sK0))) )),
% 2.63/0.72    inference(superposition,[],[f158,f60])).
% 2.63/0.72  fof(f158,plain,(
% 2.63/0.72    ( ! [X0] : (r1_tarski(k2_xboole_0(sK2,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(superposition,[],[f152,f58])).
% 2.63/0.72  fof(f152,plain,(
% 2.63/0.72    ( ! [X2] : (r1_tarski(k2_xboole_0(X2,sK2),u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.63/0.72    inference(resolution,[],[f150,f47])).
% 2.63/0.72  fof(f112,plain,(
% 2.63/0.72    spl3_5),
% 2.63/0.72    inference(avatar_contradiction_clause,[],[f111])).
% 2.63/0.72  fof(f111,plain,(
% 2.63/0.72    $false | spl3_5),
% 2.63/0.72    inference(subsumption_resolution,[],[f109,f43])).
% 2.63/0.72  fof(f109,plain,(
% 2.63/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 2.63/0.72    inference(resolution,[],[f102,f69])).
% 2.63/0.72  fof(f102,plain,(
% 2.63/0.72    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 2.63/0.72    inference(avatar_component_clause,[],[f100])).
% 2.63/0.72  fof(f100,plain,(
% 2.63/0.72    spl3_5 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.63/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.63/0.72  fof(f107,plain,(
% 2.63/0.72    ~spl3_5 | ~spl3_6),
% 2.63/0.72    inference(avatar_split_clause,[],[f97,f104,f100])).
% 2.63/0.72  fof(f97,plain,(
% 2.63/0.72    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.63/0.72    inference(superposition,[],[f45,f54])).
% 2.63/0.72  fof(f45,plain,(
% 2.63/0.72    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 2.63/0.72    inference(cnf_transformation,[],[f37])).
% 2.63/0.72  % SZS output end Proof for theBenchmark
% 2.63/0.72  % (24207)------------------------------
% 2.63/0.72  % (24207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.63/0.72  % (24207)Termination reason: Refutation
% 2.63/0.72  
% 2.63/0.72  % (24207)Memory used [KB]: 12792
% 2.63/0.72  % (24207)Time elapsed: 0.269 s
% 2.63/0.72  % (24207)------------------------------
% 2.63/0.72  % (24207)------------------------------
% 2.63/0.72  % (24200)Success in time 0.367 s
%------------------------------------------------------------------------------
