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
% DateTime   : Thu Dec  3 13:14:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 284 expanded)
%              Number of leaves         :   15 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  362 (1383 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f64,f75,f86,f91,f115,f123,f134])).

fof(f134,plain,
    ( ~ spl4_1
    | spl4_2
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | spl4_6 ),
    inference(subsumption_resolution,[],[f131,f48])).

fof(f48,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_2
  <=> r1_tarski(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f131,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl4_1
    | spl4_6 ),
    inference(resolution,[],[f130,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f130,plain,
    ( ~ r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1)
    | ~ spl4_1
    | spl4_6 ),
    inference(subsumption_resolution,[],[f129,f45])).

fof(f45,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_1
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f129,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1)
    | spl4_6 ),
    inference(resolution,[],[f127,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
      | ~ v1_tops_2(sK1,sK0) )
    & ( r1_tarski(sK1,u1_pre_topc(sK0))
      | v1_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(sK0))
            | ~ v1_tops_2(X1,sK0) )
          & ( r1_tarski(X1,u1_pre_topc(sK0))
            | v1_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,u1_pre_topc(sK0))
          | ~ v1_tops_2(X1,sK0) )
        & ( r1_tarski(X1,u1_pre_topc(sK0))
          | v1_tops_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
        | ~ v1_tops_2(sK1,sK0) )
      & ( r1_tarski(sK1,u1_pre_topc(sK0))
        | v1_tops_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> r1_tarski(X1,u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(f127,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X2,sK0)
        | ~ r2_hidden(sK3(sK1,u1_pre_topc(sK0)),X2) )
    | spl4_6 ),
    inference(resolution,[],[f125,f114])).

fof(f114,plain,
    ( ~ v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_6
  <=> v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f125,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ v1_tops_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f101,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,X1)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v3_pre_topc(X3,X0) ) ),
    inference(subsumption_resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f123,plain,
    ( spl4_2
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl4_2
    | spl4_5 ),
    inference(subsumption_resolution,[],[f120,f48])).

fof(f120,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | spl4_5 ),
    inference(resolution,[],[f118,f39])).

fof(f118,plain,
    ( ~ r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1)
    | spl4_5 ),
    inference(resolution,[],[f117,f29])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK1,u1_pre_topc(sK0)),X0) )
    | spl4_5 ),
    inference(resolution,[],[f110,f41])).

fof(f110,plain,
    ( ~ m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_5
  <=> m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f115,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_2 ),
    inference(avatar_split_clause,[],[f96,f47,f112,f108])).

fof(f96,plain,
    ( ~ v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0)
    | ~ m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f94,f28])).

fof(f94,plain,
    ( ~ v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0)
    | ~ m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_2 ),
    inference(resolution,[],[f93,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f93,plain,
    ( ~ r2_hidden(sK3(sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | spl4_2 ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f89,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f31,f49])).

fof(f49,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f31,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f84,f28])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f83,f29])).

fof(f83,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f81,f44])).

fof(f44,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f81,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f76,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f59,f29])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK2(sK0,sK1),X0) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_3
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK2(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f75,plain,
    ( spl4_1
    | ~ spl4_2
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f74])).

% (13697)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% (13704)WARNING: option uwaf not known.
fof(f74,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f73,f28])).

fof(f73,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_1
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f72,f29])).

fof(f72,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | spl4_1
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f70,f44])).

fof(f70,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_2
    | spl4_4 ),
    inference(resolution,[],[f68,f36])).

fof(f68,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl4_2
    | spl4_4 ),
    inference(resolution,[],[f66,f49])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_pre_topc(sK0))
        | ~ r2_hidden(sK2(sK0,sK1),X0) )
    | spl4_4 ),
    inference(resolution,[],[f63,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_4
  <=> r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f64,plain,
    ( spl4_3
    | ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f56,f43,f61,f58])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK2(sK0,sK1),X0) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f55,f29])).

% (13699)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% (13712)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% (13705)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% (13700)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% (13706)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
fof(f55,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK2(sK0,sK1),X0) )
    | spl4_1 ),
    inference(resolution,[],[f54,f44])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X0,sK0)
      | ~ r2_hidden(sK2(sK0,X0),u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(sK2(sK0,X0),X1) ) ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_2(X0,sK0)
      | ~ r2_hidden(sK2(sK0,X0),u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f52,f28])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X0,sK0)
      | ~ r2_hidden(sK2(sK0,X0),u1_pre_topc(sK0))
      | ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK2(sK0,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f37,f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f30,f47,f43])).

fof(f30,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (13695)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.45  % (13702)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (13696)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.46  % (13707)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (13713)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.47  % (13694)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % (13698)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (13709)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % (13709)Refutation not found, incomplete strategy% (13709)------------------------------
% 0.21/0.47  % (13709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13709)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (13709)Memory used [KB]: 895
% 0.21/0.47  % (13709)Time elapsed: 0.072 s
% 0.21/0.47  % (13709)------------------------------
% 0.21/0.47  % (13709)------------------------------
% 0.21/0.47  % (13694)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f50,f64,f75,f86,f91,f115,f123,f134])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~spl4_1 | spl4_2 | spl4_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f133])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    $false | (~spl4_1 | spl4_2 | spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f131,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ~r1_tarski(sK1,u1_pre_topc(sK0)) | spl4_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl4_2 <=> r1_tarski(sK1,u1_pre_topc(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    r1_tarski(sK1,u1_pre_topc(sK0)) | (~spl4_1 | spl4_6)),
% 0.21/0.47    inference(resolution,[],[f130,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1) | (~spl4_1 | spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f129,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    v1_tops_2(sK1,sK0) | ~spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl4_1 <=> v1_tops_2(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~v1_tops_2(sK1,sK0) | ~r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1) | spl4_6),
% 0.21/0.47    inference(resolution,[],[f127,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ((~r1_tarski(sK1,u1_pre_topc(sK0)) | ~v1_tops_2(sK1,sK0)) & (r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,u1_pre_topc(sK0)) | ~v1_tops_2(X1,sK0)) & (r1_tarski(X1,u1_pre_topc(sK0)) | v1_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X1] : ((~r1_tarski(X1,u1_pre_topc(sK0)) | ~v1_tops_2(X1,sK0)) & (r1_tarski(X1,u1_pre_topc(sK0)) | v1_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => ((~r1_tarski(sK1,u1_pre_topc(sK0)) | ~v1_tops_2(sK1,sK0)) & (r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (((~r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) & (r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v1_tops_2(X1,X0) <~> r1_tarski(X1,u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X2,sK0) | ~r2_hidden(sK3(sK1,u1_pre_topc(sK0)),X2)) ) | spl4_6),
% 0.21/0.47    inference(resolution,[],[f125,f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ~v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0) | spl4_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f112])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl4_6 <=> v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v3_pre_topc(X0,sK0) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f101,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X3,X1) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v3_pre_topc(X3,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f34,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(rectify,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    spl4_2 | spl4_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    $false | (spl4_2 | spl4_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f120,f48])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    r1_tarski(sK1,u1_pre_topc(sK0)) | spl4_5),
% 0.21/0.47    inference(resolution,[],[f118,f39])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK1,u1_pre_topc(sK0)),sK1) | spl4_5),
% 0.21/0.47    inference(resolution,[],[f117,f29])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK1,u1_pre_topc(sK0)),X0)) ) | spl4_5),
% 0.21/0.47    inference(resolution,[],[f110,f41])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ~m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl4_5 <=> m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ~spl4_5 | ~spl4_6 | spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f96,f47,f112,f108])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ~v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0) | ~m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f94,f28])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ~v3_pre_topc(sK3(sK1,u1_pre_topc(sK0)),sK0) | ~m1_subset_1(sK3(sK1,u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_2),
% 0.21/0.47    inference(resolution,[],[f93,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0)) | spl4_2),
% 0.21/0.47    inference(resolution,[],[f48,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ~spl4_1 | ~spl4_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    $false | (~spl4_1 | ~spl4_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f89,f45])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ~v1_tops_2(sK1,sK0) | ~spl4_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f31,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    r1_tarski(sK1,u1_pre_topc(sK0)) | ~spl4_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ~r1_tarski(sK1,u1_pre_topc(sK0)) | ~v1_tops_2(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl4_1 | ~spl4_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    $false | (spl4_1 | ~spl4_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f84,f28])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | (spl4_1 | ~spl4_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f83,f29])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | (spl4_1 | ~spl4_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f81,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ~v1_tops_2(sK1,sK0) | spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    v1_tops_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~spl4_3),
% 0.21/0.47    inference(resolution,[],[f76,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ~r2_hidden(sK2(sK0,sK1),sK1) | ~spl4_3),
% 0.21/0.47    inference(resolution,[],[f59,f29])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK2(sK0,sK1),X0)) ) | ~spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl4_3 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK2(sK0,sK1),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl4_1 | ~spl4_2 | spl4_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f74])).
% 0.21/0.48  % (13697)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.48  % (13704)WARNING: option uwaf not known.
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    $false | (spl4_1 | ~spl4_2 | spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f28])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (spl4_1 | ~spl4_2 | spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f29])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | (spl4_1 | ~spl4_2 | spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f44])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    v1_tops_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | (~spl4_2 | spl4_4)),
% 0.21/0.48    inference(resolution,[],[f68,f36])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~r2_hidden(sK2(sK0,sK1),sK1) | (~spl4_2 | spl4_4)),
% 0.21/0.48    inference(resolution,[],[f66,f49])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_pre_topc(sK0)) | ~r2_hidden(sK2(sK0,sK1),X0)) ) | spl4_4),
% 0.21/0.48    inference(resolution,[],[f63,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0)) | spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl4_4 <=> r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl4_3 | ~spl4_4 | spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f56,f43,f61,f58])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK2(sK0,sK1),X0)) ) | spl4_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f55,f29])).
% 0.21/0.48  % (13699)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  % (13712)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (13705)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.48  % (13700)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % (13706)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK2(sK0,sK1),X0)) ) | spl4_1),
% 0.21/0.49    inference(resolution,[],[f54,f44])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_tops_2(X0,sK0) | ~r2_hidden(sK2(sK0,X0),u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK2(sK0,X0),X1)) )),
% 0.21/0.49    inference(resolution,[],[f53,f41])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(X0,sK0) | ~r2_hidden(sK2(sK0,X0),u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f52,f28])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0) | ~r2_hidden(sK2(sK0,X0),u1_pre_topc(sK0)) | ~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f51,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_pre_topc(sK2(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f37,f28])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl4_1 | spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f47,f43])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (13694)------------------------------
% 0.21/0.49  % (13694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13694)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (13694)Memory used [KB]: 5373
% 0.21/0.49  % (13694)Time elapsed: 0.076 s
% 0.21/0.49  % (13694)------------------------------
% 0.21/0.49  % (13694)------------------------------
% 0.21/0.49  % (13708)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.49  % (13693)Success in time 0.138 s
%------------------------------------------------------------------------------
