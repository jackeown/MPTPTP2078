%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 169 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :  234 ( 566 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f60,f65,f73,f78,f83,f92,f97,f100])).

fof(f100,plain,
    ( spl5_11
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f99,f89,f40,f94])).

fof(f94,plain,
    ( spl5_11
  <=> r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f40,plain,
    ( spl5_2
  <=> r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f89,plain,
    ( spl5_10
  <=> r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f99,plain,
    ( r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK2))
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f42,f91,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f91,plain,
    ( r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f42,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f97,plain,
    ( ~ spl5_11
    | ~ spl5_3
    | spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f86,f80,f70,f45,f94])).

fof(f45,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f70,plain,
    ( spl5_7
  <=> r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f80,plain,
    ( spl5_9
  <=> m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f86,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK2))
    | ~ spl5_3
    | spl5_7
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f47,f72,f82,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f82,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f72,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f92,plain,
    ( spl5_10
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f87,f80,f75,f50,f89])).

fof(f50,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f75,plain,
    ( spl5_8
  <=> r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f87,plain,
    ( r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f52,f77,f82,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f52,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f83,plain,
    ( spl5_9
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f66,f50,f45,f35,f80])).

fof(f35,plain,
    ( spl5_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f66,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0))
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f37,f47,f52,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK3(X0,X1,X2),X2)
            & r2_hidden(sK3(X0,X1,X2),X1)
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f37,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f78,plain,
    ( spl5_8
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f67,f50,f45,f35,f75])).

fof(f67,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f37,f47,f52,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,
    ( ~ spl5_7
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f68,f50,f45,f35,f70])).

fof(f68,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f37,f47,f52,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,
    ( spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f54,f35,f62])).

fof(f62,plain,
    ( spl5_6
  <=> r2_hidden(sK4(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f54,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f37,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,
    ( ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f55,f35,f57])).

fof(f57,plain,
    ( spl5_5
  <=> r2_hidden(sK4(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f55,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f37,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(sK1,sK2)
    & r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK1,X2)
          & r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK1,X2)
        & r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(sK1,sK2)
      & r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

fof(f48,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f24,f40])).

fof(f24,plain,(
    r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f25,f35])).

fof(f25,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (12580)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.48  % (12581)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.48  % (12580)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f60,f65,f73,f78,f83,f92,f97,f100])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl5_11 | ~spl5_2 | ~spl5_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f99,f89,f40,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    spl5_11 <=> r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    spl5_2 <=> r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    spl5_10 <=> r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK2)) | (~spl5_2 | ~spl5_10)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f42,f91,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK1)) | ~spl5_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f89])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) | ~spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f40])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ~spl5_11 | ~spl5_3 | spl5_7 | ~spl5_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f86,f80,f70,f45,f94])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl5_7 <=> r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl5_9 <=> m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ~r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK2)) | (~spl5_3 | spl5_7 | ~spl5_9)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f47,f72,f82,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(nnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0)) | ~spl5_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f80])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) | spl5_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f70])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl5_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f45])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl5_10 | ~spl5_4 | ~spl5_8 | ~spl5_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f87,f80,f75,f50,f89])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    spl5_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl5_8 <=> r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    r2_hidden(k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0),sK1,sK2)),k7_setfam_1(sK0,sK1)) | (~spl5_4 | ~spl5_8 | ~spl5_9)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f52,f77,f82,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | ~spl5_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f75])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl5_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f50])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl5_9 | spl5_1 | ~spl5_3 | ~spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f66,f50,f45,f35,f80])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    spl5_1 <=> r1_tarski(sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0)) | (spl5_1 | ~spl5_3 | ~spl5_4)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f37,f47,f52,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK3(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ~r1_tarski(sK1,sK2) | spl5_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f35])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl5_8 | spl5_1 | ~spl5_3 | ~spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f67,f50,f45,f35,f75])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | (spl5_1 | ~spl5_3 | ~spl5_4)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f37,f47,f52,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ~spl5_7 | spl5_1 | ~spl5_3 | ~spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f68,f50,f45,f35,f70])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) | (spl5_1 | ~spl5_3 | ~spl5_4)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f37,f47,f52,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl5_6 | spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f54,f35,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl5_6 <=> r2_hidden(sK4(sK1,sK2),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    r2_hidden(sK4(sK1,sK2),sK1) | spl5_1),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f37,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ~spl5_5 | spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f55,f35,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl5_5 <=> r2_hidden(sK4(sK1,sK2),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ~r2_hidden(sK4(sK1,sK2),sK2) | spl5_1),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f37,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f50])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    (~r1_tarski(sK1,sK2) & r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(sK1,X2) & r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X2] : (~r1_tarski(sK1,X2) & r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(sK1,sK2) & r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(flattening,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) & r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f45])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f24,f40])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f25,f35])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ~r1_tarski(sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (12580)------------------------------
% 0.20/0.48  % (12580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (12580)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (12580)Memory used [KB]: 5373
% 0.20/0.48  % (12580)Time elapsed: 0.067 s
% 0.20/0.48  % (12580)------------------------------
% 0.20/0.48  % (12580)------------------------------
% 0.20/0.48  % (12566)Success in time 0.124 s
%------------------------------------------------------------------------------
