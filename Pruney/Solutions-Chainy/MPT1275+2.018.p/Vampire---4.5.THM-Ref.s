%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 284 expanded)
%              Number of leaves         :   19 (  85 expanded)
%              Depth                    :   18
%              Number of atoms          :  386 (1555 expanded)
%              Number of equality atoms :   59 ( 355 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f80,f95,f99,f101,f108,f110,f115,f149])).

fof(f149,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f114,f140])).

fof(f140,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f122,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f122,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k2_tops_1(sK0,sK1),X0),sK1)
      | r1_tarski(k2_tops_1(sK0,sK1),X0) ) ),
    inference(resolution,[],[f119,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_tops_1(sK0,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f70,f117])).

fof(f117,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f116,f87])).

fof(f87,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f43,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( sK1 != k2_tops_1(sK0,sK1)
      | ~ v3_tops_1(sK1,sK0) )
    & ( sK1 = k2_tops_1(sK0,sK1)
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != X1
          | ~ v3_tops_1(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = X1
          | v3_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( sK1 != k2_tops_1(sK0,sK1)
        | ~ v3_tops_1(sK1,sK0) )
      & ( sK1 = k2_tops_1(sK0,sK1)
        | v3_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

fof(f116,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f103,f102])).

fof(f102,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(global_subsumption,[],[f42,f44,f85])).

fof(f85,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f44,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f42,f86])).

fof(f86,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f114,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_5
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f115,plain,
    ( ~ spl4_5
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f111,f90,f75,f113])).

fof(f75,plain,
    ( spl4_2
  <=> sK1 = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f90,plain,
    ( spl4_3
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f111,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f91,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f91,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f110,plain,
    ( spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f109,f72,f93])).

fof(f93,plain,
    ( spl4_4
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f72,plain,
    ( spl4_1
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f109,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f42,f84])).

fof(f84,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(f108,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl4_2
    | spl4_3 ),
    inference(resolution,[],[f104,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f104,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl4_2
    | spl4_3 ),
    inference(forward_demodulation,[],[f98,f79])).

fof(f79,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f98,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f101,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f100,f93,f72])).

fof(f100,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f42,f44,f83])).

fof(f83,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | v3_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

fof(f99,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f96,f90,f93])).

fof(f96,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f42,f82])).

fof(f82,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f95,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f88,f93,f90])).

fof(f88,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f42,f81])).

fof(f81,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f45,f75,f72])).

fof(f45,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f46,f75,f72])).

fof(f46,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:33:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (26641)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (26632)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (26656)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (26631)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (26630)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (26647)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (26648)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (26648)Refutation not found, incomplete strategy% (26648)------------------------------
% 0.21/0.52  % (26648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26628)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (26629)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (26648)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26648)Memory used [KB]: 10746
% 0.21/0.53  % (26648)Time elapsed: 0.118 s
% 0.21/0.53  % (26648)------------------------------
% 0.21/0.53  % (26648)------------------------------
% 0.21/0.53  % (26627)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (26640)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (26627)Refutation not found, incomplete strategy% (26627)------------------------------
% 0.21/0.53  % (26627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26627)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26627)Memory used [KB]: 1663
% 0.21/0.53  % (26627)Time elapsed: 0.117 s
% 0.21/0.53  % (26627)------------------------------
% 0.21/0.53  % (26627)------------------------------
% 0.21/0.53  % (26629)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f77,f80,f95,f99,f101,f108,f110,f115,f149])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    spl4_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f147])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    $false | spl4_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f114,f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f139])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    r1_tarski(k2_tops_1(sK0,sK1),sK1) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.53    inference(resolution,[],[f122,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2(k2_tops_1(sK0,sK1),X0),sK1) | r1_tarski(k2_tops_1(sK0,sK1),X0)) )),
% 0.21/0.53    inference(resolution,[],[f119,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k2_tops_1(sK0,sK1)) | r2_hidden(X0,sK1)) )),
% 0.21/0.53    inference(superposition,[],[f70,f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.53    inference(superposition,[],[f116,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 0.21/0.53    inference(resolution,[],[f43,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f103,f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.53    inference(global_subsumption,[],[f42,f44,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f43,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    v4_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.21/0.53    inference(global_subsumption,[],[f42,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f43,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(rectify,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(flattening,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl4_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl4_5 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~spl4_5 | spl4_2 | ~spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f111,f90,f75,f113])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    spl4_2 <=> sK1 = k2_tops_1(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl4_3 <=> r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    sK1 = k2_tops_1(sK0,sK1) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl4_3),
% 0.21/0.53    inference(resolution,[],[f91,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl4_4 | ~spl4_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f109,f72,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl4_4 <=> v2_tops_1(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    spl4_1 <=> v3_tops_1(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ~v3_tops_1(sK1,sK0) | v2_tops_1(sK1,sK0)),
% 0.21/0.53    inference(global_subsumption,[],[f42,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ~v3_tops_1(sK1,sK0) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f43,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ~spl4_2 | spl4_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    $false | (~spl4_2 | spl4_3)),
% 0.21/0.53    inference(resolution,[],[f104,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ~r1_tarski(sK1,sK1) | (~spl4_2 | spl4_3)),
% 0.21/0.53    inference(forward_demodulation,[],[f98,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    sK1 = k2_tops_1(sK0,sK1) | ~spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f75])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl4_1 | ~spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f100,f93,f72])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ~v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0)),
% 0.21/0.53    inference(global_subsumption,[],[f42,f44,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ~v4_pre_topc(sK1,sK0) | ~v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f43,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | v3_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl4_4 | ~spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f96,f90,f93])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 0.21/0.53    inference(global_subsumption,[],[f42,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f43,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    spl4_3 | ~spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f88,f93,f90])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ~v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.53    inference(global_subsumption,[],[f42,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ~v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f43,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | r1_tarski(X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    spl4_1 | spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f75,f72])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ~spl4_1 | ~spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f46,f75,f72])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (26629)------------------------------
% 0.21/0.53  % (26629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26629)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (26629)Memory used [KB]: 10746
% 0.21/0.53  % (26629)Time elapsed: 0.127 s
% 0.21/0.53  % (26629)------------------------------
% 0.21/0.53  % (26629)------------------------------
% 0.21/0.53  % (26638)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (26652)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (26651)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (26653)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (26657)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (26655)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (26644)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (26643)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (26649)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (26646)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (26645)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (26645)Refutation not found, incomplete strategy% (26645)------------------------------
% 0.21/0.54  % (26645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26645)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26645)Memory used [KB]: 10618
% 0.21/0.54  % (26645)Time elapsed: 0.141 s
% 0.21/0.54  % (26645)------------------------------
% 0.21/0.54  % (26645)------------------------------
% 0.21/0.54  % (26654)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (26637)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (26639)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (26637)Refutation not found, incomplete strategy% (26637)------------------------------
% 0.21/0.55  % (26637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26637)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26637)Memory used [KB]: 10746
% 0.21/0.55  % (26637)Time elapsed: 0.141 s
% 0.21/0.55  % (26637)------------------------------
% 0.21/0.55  % (26637)------------------------------
% 0.21/0.55  % (26625)Success in time 0.186 s
%------------------------------------------------------------------------------
