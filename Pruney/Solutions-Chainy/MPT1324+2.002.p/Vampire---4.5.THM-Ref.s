%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 156 expanded)
%              Number of leaves         :   13 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  207 ( 686 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f223,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f123,f161,f187])).

fof(f187,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f185,f23])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))
    & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
                & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2))
            & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2))
          & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2))
        & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))
      & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
                 => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
               => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tops_2)).

fof(f185,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f184,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f184,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f183,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f183,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f178,f27])).

fof(f27,plain,(
    ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f178,plain,
    ( r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f29,f53])).

fof(f53,plain,
    ( sK1 = k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_2
  <=> sK1 = k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_2)).

fof(f161,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f160,f47,f51])).

fof(f47,plain,
    ( spl3_1
  <=> r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f160,plain,
    ( sK1 = k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f158,f26])).

fof(f26,plain,(
    r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f158,plain,
    ( sK1 = k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))
    | ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))
    | ~ spl3_1 ),
    inference(resolution,[],[f48,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f48,plain,
    ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f123,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f121,f25])).

fof(f121,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_9 ),
    inference(subsumption_resolution,[],[f120,f23])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_9 ),
    inference(subsumption_resolution,[],[f118,f24])).

fof(f118,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_9 ),
    inference(resolution,[],[f113,f109])).

fof(f109,plain,
    ( ~ r1_tarski(k1_tops_2(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | spl3_9 ),
    inference(resolution,[],[f98,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_setfam_1(X0,X1),X0)
      | ~ r1_tarski(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f73,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | r1_tarski(k5_setfam_1(X1,X0),X1) ) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f98,plain,
    ( ~ r1_tarski(k5_setfam_1(sK1,k1_tops_2(sK0,sK1,sK2)),sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_9
  <=> r1_tarski(k5_setfam_1(sK1,k1_tops_2(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f113,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k1_tops_2(X4,X5,X3),k1_zfmisc_1(X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4)))) ) ),
    inference(resolution,[],[f107,f34])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f36,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(f108,plain,
    ( ~ spl3_9
    | spl3_1 ),
    inference(avatar_split_clause,[],[f91,f47,f96])).

fof(f91,plain,
    ( ~ r1_tarski(k5_setfam_1(sK1,k1_tops_2(sK0,sK1,sK2)),sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f90,f23])).

fof(f90,plain,
    ( ~ r1_tarski(k5_setfam_1(sK1,k1_tops_2(sK0,sK1,sK2)),sK1)
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f88,f24])).

fof(f88,plain,
    ( ~ r1_tarski(k5_setfam_1(sK1,k1_tops_2(sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(superposition,[],[f49,f28])).

fof(f49,plain,
    ( ~ r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:41:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (7699)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.47  % (7699)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f223,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f108,f123,f161,f187])).
% 0.22/0.47  fof(f187,plain,(
% 0.22/0.47    ~spl3_2),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f186])).
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    $false | ~spl3_2),
% 0.22/0.47    inference(subsumption_resolution,[],[f185,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    l1_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ((~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ? [X2] : (~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tops_2)).
% 0.22/0.47  fof(f185,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | ~spl3_2),
% 0.22/0.47    inference(subsumption_resolution,[],[f184,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f184,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_2),
% 0.22/0.47    inference(subsumption_resolution,[],[f183,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f183,plain,(
% 0.22/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_2),
% 0.22/0.47    inference(subsumption_resolution,[],[f178,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f178,plain,(
% 0.22/0.47    r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_2),
% 0.22/0.47    inference(superposition,[],[f29,f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    sK1 = k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)) | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    spl3_2 <=> sK1 = k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_2)).
% 0.22/0.47  fof(f161,plain,(
% 0.22/0.47    spl3_2 | ~spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f160,f47,f51])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    spl3_1 <=> r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    sK1 = k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)) | ~spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f158,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f158,plain,(
% 0.22/0.47    sK1 = k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)) | ~r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) | ~spl3_1),
% 0.22/0.47    inference(resolution,[],[f48,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.47    inference(flattening,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.47    inference(nnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),sK1) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f47])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    spl3_9),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f122])).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    $false | spl3_9),
% 0.22/0.47    inference(subsumption_resolution,[],[f121,f25])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_9),
% 0.22/0.47    inference(subsumption_resolution,[],[f120,f23])).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_9),
% 0.22/0.47    inference(subsumption_resolution,[],[f118,f24])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_9),
% 0.22/0.47    inference(resolution,[],[f113,f109])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    ~r1_tarski(k1_tops_2(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | spl3_9),
% 0.22/0.47    inference(resolution,[],[f98,f74])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k5_setfam_1(X0,X1),X0) | ~r1_tarski(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(resolution,[],[f73,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.47    inference(nnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | r1_tarski(k5_setfam_1(X1,X0),X1)) )),
% 0.22/0.47    inference(resolution,[],[f30,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    ~r1_tarski(k5_setfam_1(sK1,k1_tops_2(sK0,sK1,sK2)),sK1) | spl3_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f96])).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    spl3_9 <=> r1_tarski(k5_setfam_1(sK1,k1_tops_2(sK0,sK1,sK2)),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ( ! [X4,X5,X3] : (r1_tarski(k1_tops_2(X4,X5,X3),k1_zfmisc_1(X5)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))) )),
% 0.22/0.47    inference(resolution,[],[f107,f34])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f106])).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(superposition,[],[f36,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    ~spl3_9 | spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f91,f47,f96])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    ~r1_tarski(k5_setfam_1(sK1,k1_tops_2(sK0,sK1,sK2)),sK1) | spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f90,f23])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    ~r1_tarski(k5_setfam_1(sK1,k1_tops_2(sK0,sK1,sK2)),sK1) | ~l1_pre_topc(sK0) | spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f88,f24])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    ~r1_tarski(k5_setfam_1(sK1,k1_tops_2(sK0,sK1,sK2)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_1),
% 0.22/0.47    inference(superposition,[],[f49,f28])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ~r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),sK1) | spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f47])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (7699)------------------------------
% 0.22/0.47  % (7699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (7699)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (7699)Memory used [KB]: 6268
% 0.22/0.47  % (7699)Time elapsed: 0.061 s
% 0.22/0.47  % (7699)------------------------------
% 0.22/0.47  % (7699)------------------------------
% 0.22/0.47  % (7694)Success in time 0.107 s
%------------------------------------------------------------------------------
