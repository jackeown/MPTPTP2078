%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 710 expanded)
%              Number of leaves         :   19 ( 266 expanded)
%              Depth                    :   19
%              Number of atoms          :  391 (4188 expanded)
%              Number of equality atoms :   67 ( 735 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f282,f379])).

fof(f379,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f371,f42])).

fof(f42,plain,(
    ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v4_pre_topc(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v4_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v4_pre_topc(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v4_pre_topc(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v4_pre_topc(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v4_pre_topc(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v4_pre_topc(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & v4_pre_topc(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ v4_pre_topc(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v4_pre_topc(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(f371,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f180,f365])).

fof(f365,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | ~ spl6_4 ),
    inference(resolution,[],[f361,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X0),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(factoring,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f58,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f361,plain,
    ( ~ r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f299,f80])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f40,f79])).

fof(f79,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f78,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f76,f38])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f74,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),X0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f298,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f298,plain,
    ( ~ r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2))
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f286,f42])).

fof(f286,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2))
    | ~ spl6_4 ),
    inference(superposition,[],[f180,f147])).

fof(f147,plain,(
    ! [X8,X9] :
      ( k1_setfam_1(k2_tarski(X8,X9)) = X8
      | ~ r2_hidden(sK5(X8,X9,X8),X9) ) ),
    inference(subsumption_resolution,[],[f142,f108])).

fof(f142,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK5(X8,X9,X8),X9)
      | ~ r2_hidden(sK5(X8,X9,X8),X8)
      | k1_setfam_1(k2_tarski(X8,X9)) = X8 ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK5(X8,X9,X8),X9)
      | ~ r2_hidden(sK5(X8,X9,X8),X8)
      | k1_setfam_1(k2_tarski(X8,X9)) = X8
      | k1_setfam_1(k2_tarski(X8,X9)) = X8 ) ),
    inference(resolution,[],[f64,f108])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f60,f51])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f180,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl6_4
  <=> v4_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f282,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f274,f80])).

fof(f274,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | spl6_3 ),
    inference(backward_demodulation,[],[f176,f269])).

fof(f269,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2)))
    | spl6_3 ),
    inference(resolution,[],[f266,f108])).

fof(f266,plain,
    ( ~ r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),sK3)
    | spl6_3 ),
    inference(resolution,[],[f197,f80])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),X0) )
    | spl6_3 ),
    inference(resolution,[],[f187,f52])).

fof(f187,plain,
    ( ~ r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2))
    | spl6_3 ),
    inference(subsumption_resolution,[],[f184,f80])).

fof(f184,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2))
    | spl6_3 ),
    inference(superposition,[],[f176,f147])).

fof(f176,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_3
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f181,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f172,f178,f174])).

fof(f172,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f171,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f171,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),sK2)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f170,f96])).

fof(f96,plain,(
    ! [X2] : k1_setfam_1(k2_tarski(X2,sK3)) = k9_subset_1(k2_struct_0(sK2),sK3,X2) ),
    inference(subsumption_resolution,[],[f93,f80])).

fof(f93,plain,(
    ! [X2] :
      ( k1_setfam_1(k2_tarski(X2,sK3)) = k9_subset_1(k2_struct_0(sK2),sK3,X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    inference(superposition,[],[f84,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f84,plain,(
    ! [X1] : k9_subset_1(k2_struct_0(sK2),X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3)) ),
    inference(resolution,[],[f63,f80])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f170,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))
    | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f169,f50])).

fof(f169,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_struct_0(sK2)))
    | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f168,f96])).

fof(f168,plain,
    ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f166,f77])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f62,f75])).

fof(f75,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f74,f36])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f41,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f166,plain,
    ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2) ),
    inference(resolution,[],[f165,f61])).

fof(f61,plain,(
    v4_pre_topc(sK3,sK0) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f39,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f165,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) ) ),
    inference(forward_demodulation,[],[f164,f79])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) ) ),
    inference(forward_demodulation,[],[f163,f79])).

fof(f163,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) ) ),
    inference(forward_demodulation,[],[f162,f75])).

fof(f162,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) ) ),
    inference(subsumption_resolution,[],[f161,f36])).

fof(f161,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f70,f38])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:28:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (4826)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (4817)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (4805)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (4809)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (4812)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (4812)Refutation not found, incomplete strategy% (4812)------------------------------
% 0.21/0.51  % (4812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4812)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4812)Memory used [KB]: 10746
% 0.21/0.51  % (4812)Time elapsed: 0.102 s
% 0.21/0.51  % (4812)------------------------------
% 0.21/0.51  % (4812)------------------------------
% 0.21/0.51  % (4806)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (4813)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (4831)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (4802)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (4814)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (4815)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (4827)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (4816)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (4805)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f181,f282,f379])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    ~spl6_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f378])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    $false | ~spl6_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f371,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ~v4_pre_topc(sK3,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    (((~v4_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25,f24,f23,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) => (? [X3] : (~v4_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X3] : (~v4_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => (~v4_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    v4_pre_topc(sK3,sK2) | ~spl6_4),
% 0.21/0.53    inference(backward_demodulation,[],[f180,f365])).
% 0.21/0.53  fof(f365,plain,(
% 0.21/0.53    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | ~spl6_4),
% 0.21/0.53    inference(resolution,[],[f361,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X0),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.21/0.53    inference(factoring,[],[f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f58,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(rectify,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.53  fof(f361,plain,(
% 0.21/0.53    ~r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),sK3) | ~spl6_4),
% 0.21/0.53    inference(resolution,[],[f299,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.53    inference(backward_demodulation,[],[f40,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f78,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    u1_struct_0(sK2) = k2_struct_0(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f76,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(resolution,[],[f74,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(resolution,[],[f43,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),X0)) ) | ~spl6_4),
% 0.21/0.53    inference(resolution,[],[f298,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    ~r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2)) | ~spl6_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f286,f42])).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    v4_pre_topc(sK3,sK2) | ~r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2)) | ~spl6_4),
% 0.21/0.53    inference(superposition,[],[f180,f147])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ( ! [X8,X9] : (k1_setfam_1(k2_tarski(X8,X9)) = X8 | ~r2_hidden(sK5(X8,X9,X8),X9)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f142,f108])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    ( ! [X8,X9] : (~r2_hidden(sK5(X8,X9,X8),X9) | ~r2_hidden(sK5(X8,X9,X8),X8) | k1_setfam_1(k2_tarski(X8,X9)) = X8) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ( ! [X8,X9] : (~r2_hidden(sK5(X8,X9,X8),X9) | ~r2_hidden(sK5(X8,X9,X8),X8) | k1_setfam_1(k2_tarski(X8,X9)) = X8 | k1_setfam_1(k2_tarski(X8,X9)) = X8) )),
% 0.21/0.53    inference(resolution,[],[f64,f108])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f60,f51])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    v4_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2) | ~spl6_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f178])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    spl6_4 <=> v4_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    spl6_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f281])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    $false | spl6_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f274,f80])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | spl6_3),
% 0.21/0.53    inference(backward_demodulation,[],[f176,f269])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))) | spl6_3),
% 0.21/0.53    inference(resolution,[],[f266,f108])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    ~r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),sK3) | spl6_3),
% 0.21/0.53    inference(resolution,[],[f197,f80])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),X0)) ) | spl6_3),
% 0.21/0.53    inference(resolution,[],[f187,f52])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ~r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2)) | spl6_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f184,f80])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | ~r2_hidden(sK5(sK3,k2_struct_0(sK2),sK3),k2_struct_0(sK2)) | spl6_3),
% 0.21/0.53    inference(superposition,[],[f176,f147])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    ~m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | spl6_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f174])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    spl6_3 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    ~spl6_3 | spl6_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f172,f178,f174])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    v4_pre_topc(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),sK2) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.53    inference(forward_demodulation,[],[f171,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    v4_pre_topc(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),sK2) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.53    inference(forward_demodulation,[],[f170,f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X2] : (k1_setfam_1(k2_tarski(X2,sK3)) = k9_subset_1(k2_struct_0(sK2),sK3,X2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f93,f80])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X2] : (k1_setfam_1(k2_tarski(X2,sK3)) = k9_subset_1(k2_struct_0(sK2),sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))) )),
% 0.21/0.53    inference(superposition,[],[f84,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X1] : (k9_subset_1(k2_struct_0(sK2),X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) )),
% 0.21/0.53    inference(resolution,[],[f63,f80])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f53,f51])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    ~m1_subset_1(k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK2))),k1_zfmisc_1(k2_struct_0(sK2))) | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f169,f50])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ~m1_subset_1(k1_setfam_1(k2_tarski(k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_struct_0(sK2))) | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f168,f96])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f166,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.53    inference(backward_demodulation,[],[f62,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f74,f36])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(definition_unfolding,[],[f37,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    sK1 = sK3),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2)),
% 0.21/0.53    inference(resolution,[],[f165,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    v4_pre_topc(sK3,sK0)),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f41])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    v4_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f164,f79])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f163,f79])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f162,f75])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f161,f36])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~l1_pre_topc(sK0)) )),
% 0.21/0.53    inference(resolution,[],[f70,f38])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(rectify,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (4805)------------------------------
% 0.21/0.53  % (4805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4805)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (4805)Memory used [KB]: 10874
% 0.21/0.53  % (4805)Time elapsed: 0.120 s
% 0.21/0.53  % (4805)------------------------------
% 0.21/0.53  % (4805)------------------------------
% 0.21/0.53  % (4803)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (4799)Success in time 0.171 s
%------------------------------------------------------------------------------
