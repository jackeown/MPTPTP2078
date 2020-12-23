%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t31_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:38 EDT 2019

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 151 expanded)
%              Number of leaves         :   19 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  306 ( 558 expanded)
%              Number of equality atoms :   31 (  48 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f322,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f298,f302,f311,f321])).

fof(f321,plain,
    ( ~ spl10_0
    | ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f312,f275])).

fof(f275,plain,
    ( l1_struct_0(sK1)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl10_0
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f312,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f308,f173])).

fof(f173,plain,(
    ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f171,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_setfam_1(X0),k9_setfam_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f114,f90,f90])).

fof(f90,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',redefinition_k9_setfam_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t79_zfmisc_1)).

fof(f171,plain,(
    ~ r1_tarski(k9_setfam_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f170,f130])).

fof(f130,plain,(
    m1_subset_1(sK2,k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f87,f90,f90])).

fof(f87,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f67,f66,f65])).

fof(f65,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
        & m1_pre_topc(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t31_tops_2)).

fof(f170,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK2,k9_setfam_1(X2))
      | ~ r1_tarski(X2,k9_setfam_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f168,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f116,f90])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t3_subset)).

fof(f168,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | ~ r1_tarski(X0,k9_setfam_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f166,f129])).

fof(f129,plain,(
    ~ m1_subset_1(sK2,k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f88,f90,f90])).

fof(f88,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f68])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k9_setfam_1(X1))
      | ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f125,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f117,f90])).

fof(f117,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t1_xboole_1)).

fof(f308,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | ~ spl10_6 ),
    inference(superposition,[],[f297,f93])).

fof(f93,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',d3_struct_0)).

fof(f297,plain,
    ( r1_tarski(k2_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl10_6
  <=> r1_tarski(k2_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f311,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f309,f85])).

fof(f85,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f309,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_1 ),
    inference(resolution,[],[f303,f86])).

fof(f86,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f303,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_1 ),
    inference(resolution,[],[f299,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',dt_m1_pre_topc)).

fof(f299,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl10_1 ),
    inference(resolution,[],[f278,f95])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',dt_l1_pre_topc)).

fof(f278,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl10_1
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f302,plain,(
    spl10_5 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f300,f85])).

fof(f300,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_5 ),
    inference(resolution,[],[f291,f95])).

fof(f291,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl10_5
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f298,plain,
    ( ~ spl10_5
    | spl10_6 ),
    inference(avatar_split_clause,[],[f272,f296,f290])).

fof(f272,plain,
    ( r1_tarski(k2_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f269,f93])).

fof(f269,plain,(
    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f266,f85])).

fof(f266,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f233,f86])).

fof(f233,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f97,f107])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1),k2_struct_0(X1)) = sK3(X0,X1)
                    & r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
                    & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X5),k2_struct_0(X1)) = X5
                          & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X0))
                          & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f71,f74,f73,f72])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,u1_pre_topc(X1)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                & r2_hidden(X4,u1_pre_topc(X0))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,u1_pre_topc(X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK3(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X0))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & r2_hidden(X4,u1_pre_topc(X0))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1),k2_struct_0(X1)) = X2
        & r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
          & r2_hidden(X7,u1_pre_topc(X0))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X5),k2_struct_0(X1)) = X5
        & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X4] :
                        ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                        & r2_hidden(X4,u1_pre_topc(X0))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X7] :
                            ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
                            & r2_hidden(X7,u1_pre_topc(X0))
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',d9_pre_topc)).
%------------------------------------------------------------------------------
