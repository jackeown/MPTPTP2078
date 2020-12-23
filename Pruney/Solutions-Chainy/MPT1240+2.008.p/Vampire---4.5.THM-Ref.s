%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:16 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  193 (1322 expanded)
%              Number of leaves         :   42 ( 410 expanded)
%              Depth                    :   28
%              Number of atoms          :  619 (7842 expanded)
%              Number of equality atoms :  119 ( 544 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f646,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f154,f159,f164,f169,f174,f608,f643])).

fof(f643,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f642])).

fof(f642,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f619,f251])).

fof(f251,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f186,f246])).

fof(f246,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f175,f98])).

fof(f98,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f175,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f83,f99])).

fof(f99,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f83,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f69,f72,f71,f70])).

fof(f70,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X1,k1_tops_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X2,X1] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ? [X2,X1] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X1,X3)
              | ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ r2_hidden(X1,k1_tops_1(sK0,X2)) )
        & ( ? [X4] :
              ( r2_hidden(X1,X4)
              & r1_tarski(X4,X2)
              & v3_pre_topc(X4,sK0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | r2_hidden(X1,k1_tops_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(sK1,X3)
            | ~ r1_tarski(X3,sK2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
      & ( ? [X4] :
            ( r2_hidden(sK1,X4)
            & r1_tarski(X4,sK2)
            & v3_pre_topc(X4,sK0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ? [X4] :
        ( r2_hidden(sK1,X4)
        & r1_tarski(X4,sK2)
        & v3_pre_topc(X4,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK1,sK3)
      & r1_tarski(sK3,sK2)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,k1_tops_1(X0,X2))
            <=> ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(f186,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f83,f84,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f73])).

fof(f619,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f183,f185,f149,f614])).

fof(f614,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK0)
        | ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X3,sK2) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f153,f246])).

fof(f153,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl5_2
  <=> ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f149,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_1
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f185,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f82,f83,f84,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f82,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f183,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f83,f84,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f608,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f607])).

fof(f607,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f601,f158])).

fof(f158,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f601,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f473,f593])).

fof(f593,plain,
    ( sK3 = k1_tops_1(sK0,sK3)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f576,f342])).

fof(f342,plain,
    ( sK3 = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3)
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f269,f336])).

fof(f336,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f91,f94,f292,f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f292,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f291,f286])).

fof(f286,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f283,f133])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f93,f105])).

fof(f105,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f283,plain,(
    k1_tops_1(sK0,k1_xboole_0) = k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f176,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f112,f105])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f176,plain,(
    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f92,f83,f100])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f291,plain,(
    ! [X0] : r1_xboole_0(k1_tops_1(sK0,k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f282,f95])).

fof(f95,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f282,plain,(
    ! [X0] : r1_xboole_0(k1_tops_1(sK0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f176,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f94,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f91,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f269,plain,
    ( k2_xboole_0(k1_xboole_0,sK3) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3)
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f228,f246])).

fof(f228,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK3) = k2_xboole_0(k1_xboole_0,sK3)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f92,f173,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f173,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f576,plain,
    ( k1_tops_1(sK0,sK3) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f564,f571])).

fof(f571,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f520,f343])).

fof(f343,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f338,f336])).

fof(f338,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) ),
    inference(unit_resulting_resolution,[],[f292,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f520,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f437,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f437,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f90,f432,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f432,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f359,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f110,f97])).

fof(f97,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f359,plain,(
    ! [X0,X1] : ~ r1_xboole_0(k2_tarski(X0,X1),k1_zfmisc_1(X1)) ),
    inference(unit_resulting_resolution,[],[f144,f134,f344,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f344,plain,(
    ! [X1] : k1_xboole_0 != k2_tarski(X1,X1) ),
    inference(backward_demodulation,[],[f142,f343])).

fof(f142,plain,(
    ! [X1] : k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f120,f97,f97,f97])).

fof(f120,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f134,plain,(
    ! [X0] : r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f96,f97])).

fof(f96,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f144,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f130,f97])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f90,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f564,plain,
    ( k1_tops_1(sK0,sK3) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f563,f553])).

fof(f553,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK3))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f278,f551])).

fof(f551,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK3))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f262,f531])).

fof(f531,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f437,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f262,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f212,f246])).

fof(f212,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK3))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f83,f168,f173,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v2_pre_topc(X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v2_pre_topc(X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).

fof(f168,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl5_5
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f278,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK3)))
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f244,f246])).

fof(f244,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f211,f216])).

fof(f216,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK3) = k4_xboole_0(u1_struct_0(sK0),sK3)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f173,f113])).

fof(f211,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f83,f173,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f563,plain,
    ( k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK3))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f525,f531])).

fof(f525,plain,
    ( k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f245,f437,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(f245,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f232,f175])).

fof(f232,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(superposition,[],[f173,f98])).

fof(f473,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f150,f213,f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f76,f77])).

fof(f77,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
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

fof(f213,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f83,f163,f84,f173,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f163,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl5_4
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f150,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f148])).

fof(f174,plain,
    ( spl5_1
    | spl5_6 ),
    inference(avatar_split_clause,[],[f85,f171,f148])).

fof(f85,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f73])).

fof(f169,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f86,f166,f148])).

fof(f86,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f73])).

fof(f164,plain,
    ( spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f87,f161,f148])).

fof(f87,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f73])).

fof(f159,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f88,f156,f148])).

fof(f88,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f73])).

fof(f154,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f89,f152,f148])).

fof(f89,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:41:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (8248)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.49  % (8224)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (8240)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (8238)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (8231)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (8233)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (8227)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (8220)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (8223)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (8236)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (8245)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.57  % (8221)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.58  % (8219)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.58  % (8242)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.58  % (8222)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.58  % (8225)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.59  % (8229)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.59  % (8230)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.59  % (8234)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.59  % (8235)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.60  % (8241)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.60  % (8239)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.60  % (8237)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.85/0.60  % (8244)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.85/0.60  % (8226)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.85/0.61  % (8228)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.85/0.61  % (8247)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.85/0.61  % (8232)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.85/0.62  % (8243)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.85/0.62  % (8246)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.01/0.63  % (8245)Refutation found. Thanks to Tanya!
% 2.01/0.63  % SZS status Theorem for theBenchmark
% 2.01/0.63  % SZS output start Proof for theBenchmark
% 2.01/0.63  fof(f646,plain,(
% 2.01/0.63    $false),
% 2.01/0.63    inference(avatar_sat_refutation,[],[f154,f159,f164,f169,f174,f608,f643])).
% 2.01/0.63  fof(f643,plain,(
% 2.01/0.63    ~spl5_1 | ~spl5_2),
% 2.01/0.63    inference(avatar_contradiction_clause,[],[f642])).
% 2.01/0.63  fof(f642,plain,(
% 2.01/0.63    $false | (~spl5_1 | ~spl5_2)),
% 2.01/0.63    inference(subsumption_resolution,[],[f619,f251])).
% 2.01/0.63  fof(f251,plain,(
% 2.01/0.63    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.01/0.63    inference(backward_demodulation,[],[f186,f246])).
% 2.01/0.63  fof(f246,plain,(
% 2.01/0.63    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f175,f98])).
% 2.01/0.63  fof(f98,plain,(
% 2.01/0.63    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f37])).
% 2.01/0.63  fof(f37,plain,(
% 2.01/0.63    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.01/0.63    inference(ennf_transformation,[],[f25])).
% 2.01/0.63  fof(f25,axiom,(
% 2.01/0.63    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.01/0.63  fof(f175,plain,(
% 2.01/0.63    l1_struct_0(sK0)),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f83,f99])).
% 2.01/0.63  fof(f99,plain,(
% 2.01/0.63    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f38])).
% 2.01/0.63  fof(f38,plain,(
% 2.01/0.63    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.01/0.63    inference(ennf_transformation,[],[f26])).
% 2.01/0.63  fof(f26,axiom,(
% 2.01/0.63    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.01/0.63  fof(f83,plain,(
% 2.01/0.63    l1_pre_topc(sK0)),
% 2.01/0.63    inference(cnf_transformation,[],[f73])).
% 2.01/0.63  fof(f73,plain,(
% 2.01/0.63    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.01/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f69,f72,f71,f70])).
% 2.01/0.63  fof(f70,plain,(
% 2.01/0.63    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.01/0.63    introduced(choice_axiom,[])).
% 2.01/0.63  fof(f71,plain,(
% 2.01/0.63    ? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.01/0.63    introduced(choice_axiom,[])).
% 2.01/0.63  fof(f72,plain,(
% 2.01/0.63    ? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.01/0.63    introduced(choice_axiom,[])).
% 2.01/0.63  fof(f69,plain,(
% 2.01/0.63    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.01/0.63    inference(rectify,[],[f68])).
% 2.01/0.63  fof(f68,plain,(
% 2.01/0.63    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.01/0.63    inference(flattening,[],[f67])).
% 2.01/0.63  fof(f67,plain,(
% 2.01/0.63    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.01/0.63    inference(nnf_transformation,[],[f36])).
% 2.01/0.63  fof(f36,plain,(
% 2.01/0.63    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.01/0.63    inference(flattening,[],[f35])).
% 2.01/0.63  fof(f35,plain,(
% 2.01/0.63    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.01/0.63    inference(ennf_transformation,[],[f34])).
% 2.01/0.63  fof(f34,negated_conjecture,(
% 2.01/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.01/0.63    inference(negated_conjecture,[],[f33])).
% 2.01/0.63  fof(f33,conjecture,(
% 2.01/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).
% 2.01/0.63  fof(f186,plain,(
% 2.01/0.63    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f83,f84,f116])).
% 2.01/0.63  fof(f116,plain,(
% 2.01/0.63    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f54])).
% 2.01/0.63  fof(f54,plain,(
% 2.01/0.63    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.01/0.63    inference(flattening,[],[f53])).
% 2.01/0.63  fof(f53,plain,(
% 2.01/0.63    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.01/0.63    inference(ennf_transformation,[],[f29])).
% 2.01/0.63  fof(f29,axiom,(
% 2.01/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 2.01/0.63  fof(f84,plain,(
% 2.01/0.63    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.01/0.63    inference(cnf_transformation,[],[f73])).
% 2.01/0.63  fof(f619,plain,(
% 2.01/0.63    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl5_1 | ~spl5_2)),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f183,f185,f149,f614])).
% 2.01/0.63  fof(f614,plain,(
% 2.01/0.63    ( ! [X3] : (~v3_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,sK2)) ) | ~spl5_2),
% 2.01/0.63    inference(forward_demodulation,[],[f153,f246])).
% 2.01/0.63  fof(f153,plain,(
% 2.01/0.63    ( ! [X3] : (~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2)) ) | ~spl5_2),
% 2.01/0.63    inference(avatar_component_clause,[],[f152])).
% 2.01/0.63  fof(f152,plain,(
% 2.01/0.63    spl5_2 <=> ! [X3] : (~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2))),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.01/0.63  fof(f149,plain,(
% 2.01/0.63    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl5_1),
% 2.01/0.63    inference(avatar_component_clause,[],[f148])).
% 2.01/0.63  fof(f148,plain,(
% 2.01/0.63    spl5_1 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.01/0.63  fof(f185,plain,(
% 2.01/0.63    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f82,f83,f84,f115])).
% 2.01/0.63  fof(f115,plain,(
% 2.01/0.63    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f52])).
% 2.01/0.63  fof(f52,plain,(
% 2.01/0.63    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.01/0.63    inference(flattening,[],[f51])).
% 2.01/0.63  fof(f51,plain,(
% 2.01/0.63    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.01/0.63    inference(ennf_transformation,[],[f30])).
% 2.01/0.63  fof(f30,axiom,(
% 2.01/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.01/0.63  fof(f82,plain,(
% 2.01/0.63    v2_pre_topc(sK0)),
% 2.01/0.63    inference(cnf_transformation,[],[f73])).
% 2.01/0.63  fof(f183,plain,(
% 2.01/0.63    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f83,f84,f100])).
% 2.01/0.63  fof(f100,plain,(
% 2.01/0.63    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f39])).
% 2.01/0.63  fof(f39,plain,(
% 2.01/0.63    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.63    inference(ennf_transformation,[],[f31])).
% 2.01/0.63  fof(f31,axiom,(
% 2.01/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.01/0.63  fof(f608,plain,(
% 2.01/0.63    spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6),
% 2.01/0.63    inference(avatar_contradiction_clause,[],[f607])).
% 2.01/0.63  fof(f607,plain,(
% 2.01/0.63    $false | (spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 2.01/0.63    inference(subsumption_resolution,[],[f601,f158])).
% 2.01/0.63  fof(f158,plain,(
% 2.01/0.63    r2_hidden(sK1,sK3) | ~spl5_3),
% 2.01/0.63    inference(avatar_component_clause,[],[f156])).
% 2.01/0.63  fof(f156,plain,(
% 2.01/0.63    spl5_3 <=> r2_hidden(sK1,sK3)),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.01/0.63  fof(f601,plain,(
% 2.01/0.63    ~r2_hidden(sK1,sK3) | (spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 2.01/0.63    inference(backward_demodulation,[],[f473,f593])).
% 2.01/0.63  fof(f593,plain,(
% 2.01/0.63    sK3 = k1_tops_1(sK0,sK3) | (~spl5_5 | ~spl5_6)),
% 2.01/0.63    inference(forward_demodulation,[],[f576,f342])).
% 2.01/0.63  fof(f342,plain,(
% 2.01/0.63    sK3 = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3) | ~spl5_6),
% 2.01/0.63    inference(backward_demodulation,[],[f269,f336])).
% 2.01/0.63  fof(f336,plain,(
% 2.01/0.63    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f91,f94,f292,f132])).
% 2.01/0.63  fof(f132,plain,(
% 2.01/0.63    ( ! [X2,X0,X3,X1] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f66])).
% 2.01/0.63  fof(f66,plain,(
% 2.01/0.63    ! [X0,X1,X2,X3] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3))),
% 2.01/0.63    inference(flattening,[],[f65])).
% 2.01/0.63  fof(f65,plain,(
% 2.01/0.63    ! [X0,X1,X2,X3] : (X1 = X2 | (~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)))),
% 2.01/0.63    inference(ennf_transformation,[],[f9])).
% 2.01/0.63  fof(f9,axiom,(
% 2.01/0.63    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.01/0.63  fof(f292,plain,(
% 2.01/0.63    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.01/0.63    inference(forward_demodulation,[],[f291,f286])).
% 2.01/0.63  fof(f286,plain,(
% 2.01/0.63    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 2.01/0.63    inference(forward_demodulation,[],[f283,f133])).
% 2.01/0.63  fof(f133,plain,(
% 2.01/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.01/0.63    inference(definition_unfolding,[],[f93,f105])).
% 2.01/0.63  fof(f105,plain,(
% 2.01/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f6])).
% 2.01/0.63  fof(f6,axiom,(
% 2.01/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.01/0.63  fof(f93,plain,(
% 2.01/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f4])).
% 2.01/0.63  fof(f4,axiom,(
% 2.01/0.63    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.01/0.63  fof(f283,plain,(
% 2.01/0.63    k1_tops_1(sK0,k1_xboole_0) = k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0))),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f176,f136])).
% 2.01/0.63  fof(f136,plain,(
% 2.01/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.01/0.63    inference(definition_unfolding,[],[f112,f105])).
% 2.01/0.63  fof(f112,plain,(
% 2.01/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f48])).
% 2.01/0.63  fof(f48,plain,(
% 2.01/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.01/0.63    inference(ennf_transformation,[],[f3])).
% 2.01/0.63  fof(f3,axiom,(
% 2.01/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.01/0.63  fof(f176,plain,(
% 2.01/0.63    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f92,f83,f100])).
% 2.01/0.63  fof(f92,plain,(
% 2.01/0.63    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f23])).
% 2.01/0.63  fof(f23,axiom,(
% 2.01/0.63    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.01/0.63  fof(f291,plain,(
% 2.01/0.63    ( ! [X0] : (r1_xboole_0(k1_tops_1(sK0,k1_xboole_0),X0)) )),
% 2.01/0.63    inference(forward_demodulation,[],[f282,f95])).
% 2.01/0.63  fof(f95,plain,(
% 2.01/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.01/0.63    inference(cnf_transformation,[],[f5])).
% 2.01/0.63  fof(f5,axiom,(
% 2.01/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.01/0.63  fof(f282,plain,(
% 2.01/0.63    ( ! [X0] : (r1_xboole_0(k1_tops_1(sK0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) )),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f176,f122])).
% 2.01/0.63  fof(f122,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f56])).
% 2.01/0.63  fof(f56,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.01/0.63    inference(ennf_transformation,[],[f10])).
% 2.01/0.63  fof(f10,axiom,(
% 2.01/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.01/0.63  fof(f94,plain,(
% 2.01/0.63    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.01/0.63    inference(cnf_transformation,[],[f2])).
% 2.01/0.63  fof(f2,axiom,(
% 2.01/0.63    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.01/0.63  fof(f91,plain,(
% 2.01/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f7])).
% 2.01/0.63  fof(f7,axiom,(
% 2.01/0.63    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.01/0.63  fof(f269,plain,(
% 2.01/0.63    k2_xboole_0(k1_xboole_0,sK3) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3) | ~spl5_6),
% 2.01/0.63    inference(backward_demodulation,[],[f228,f246])).
% 2.01/0.63  fof(f228,plain,(
% 2.01/0.63    k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK3) = k2_xboole_0(k1_xboole_0,sK3) | ~spl5_6),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f92,f173,f126])).
% 2.01/0.63  fof(f126,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f63])).
% 2.01/0.63  fof(f63,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.01/0.63    inference(flattening,[],[f62])).
% 2.01/0.63  fof(f62,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.01/0.63    inference(ennf_transformation,[],[f20])).
% 2.01/0.63  fof(f20,axiom,(
% 2.01/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.01/0.63  fof(f173,plain,(
% 2.01/0.63    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_6),
% 2.01/0.63    inference(avatar_component_clause,[],[f171])).
% 2.01/0.63  fof(f171,plain,(
% 2.01/0.63    spl5_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.01/0.63  fof(f576,plain,(
% 2.01/0.63    k1_tops_1(sK0,sK3) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3) | (~spl5_5 | ~spl5_6)),
% 2.01/0.63    inference(backward_demodulation,[],[f564,f571])).
% 2.01/0.63  fof(f571,plain,(
% 2.01/0.63    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 2.01/0.63    inference(forward_demodulation,[],[f520,f343])).
% 2.01/0.63  fof(f343,plain,(
% 2.01/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.01/0.63    inference(backward_demodulation,[],[f338,f336])).
% 2.01/0.63  fof(f338,plain,(
% 2.01/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0)) )),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f292,f111])).
% 2.01/0.63  fof(f111,plain,(
% 2.01/0.63    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f47])).
% 2.01/0.63  fof(f47,plain,(
% 2.01/0.63    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.01/0.63    inference(ennf_transformation,[],[f11])).
% 2.01/0.63  fof(f11,axiom,(
% 2.01/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 2.01/0.63  fof(f520,plain,(
% 2.01/0.63    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f437,f113])).
% 2.01/0.63  fof(f113,plain,(
% 2.01/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f49])).
% 2.01/0.63  fof(f49,plain,(
% 2.01/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.01/0.63    inference(ennf_transformation,[],[f18])).
% 2.01/0.63  fof(f18,axiom,(
% 2.01/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.01/0.63  fof(f437,plain,(
% 2.01/0.63    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f90,f432,f107])).
% 2.01/0.63  fof(f107,plain,(
% 2.01/0.63    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f74])).
% 2.01/0.63  fof(f74,plain,(
% 2.01/0.63    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.01/0.63    inference(nnf_transformation,[],[f45])).
% 2.01/0.63  fof(f45,plain,(
% 2.01/0.63    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.01/0.63    inference(ennf_transformation,[],[f17])).
% 2.01/0.63  fof(f17,axiom,(
% 2.01/0.63    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.01/0.63  fof(f432,plain,(
% 2.01/0.63    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f359,f135])).
% 2.01/0.63  fof(f135,plain,(
% 2.01/0.63    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.01/0.63    inference(definition_unfolding,[],[f110,f97])).
% 2.01/0.63  fof(f97,plain,(
% 2.01/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f12])).
% 2.01/0.63  fof(f12,axiom,(
% 2.01/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.01/0.63  fof(f110,plain,(
% 2.01/0.63    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f46])).
% 2.01/0.63  fof(f46,plain,(
% 2.01/0.63    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.01/0.63    inference(ennf_transformation,[],[f15])).
% 2.01/0.63  fof(f15,axiom,(
% 2.01/0.63    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).
% 2.01/0.63  fof(f359,plain,(
% 2.01/0.63    ( ! [X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),k1_zfmisc_1(X1))) )),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f144,f134,f344,f125])).
% 2.01/0.63  fof(f125,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f61])).
% 2.01/0.63  fof(f61,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.01/0.63    inference(flattening,[],[f60])).
% 2.01/0.63  fof(f60,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.01/0.63    inference(ennf_transformation,[],[f8])).
% 2.01/0.63  fof(f8,axiom,(
% 2.01/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 2.01/0.63  fof(f344,plain,(
% 2.01/0.63    ( ! [X1] : (k1_xboole_0 != k2_tarski(X1,X1)) )),
% 2.01/0.63    inference(backward_demodulation,[],[f142,f343])).
% 2.01/0.63  fof(f142,plain,(
% 2.01/0.63    ( ! [X1] : (k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 2.01/0.63    inference(equality_resolution,[],[f138])).
% 2.01/0.63  fof(f138,plain,(
% 2.01/0.63    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) )),
% 2.01/0.63    inference(definition_unfolding,[],[f120,f97,f97,f97])).
% 2.01/0.63  fof(f120,plain,(
% 2.01/0.63    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f79])).
% 2.01/0.63  fof(f79,plain,(
% 2.01/0.63    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 2.01/0.63    inference(nnf_transformation,[],[f13])).
% 2.01/0.63  fof(f13,axiom,(
% 2.01/0.63    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 2.01/0.63  fof(f134,plain,(
% 2.01/0.63    ( ! [X0] : (r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0))) )),
% 2.01/0.63    inference(definition_unfolding,[],[f96,f97])).
% 2.01/0.63  fof(f96,plain,(
% 2.01/0.63    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f16])).
% 2.01/0.63  fof(f16,axiom,(
% 2.01/0.63    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 2.01/0.63  fof(f144,plain,(
% 2.01/0.63    ( ! [X2,X1] : (r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2))) )),
% 2.01/0.63    inference(equality_resolution,[],[f139])).
% 2.01/0.63  fof(f139,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X2,X2) != X0) )),
% 2.01/0.63    inference(definition_unfolding,[],[f130,f97])).
% 2.01/0.63  fof(f130,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 2.01/0.63    inference(cnf_transformation,[],[f81])).
% 2.01/0.63  fof(f81,plain,(
% 2.01/0.63    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.01/0.63    inference(flattening,[],[f80])).
% 2.01/0.63  fof(f80,plain,(
% 2.01/0.63    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.01/0.63    inference(nnf_transformation,[],[f64])).
% 2.01/0.63  fof(f64,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.01/0.63    inference(ennf_transformation,[],[f14])).
% 2.01/0.63  fof(f14,axiom,(
% 2.01/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).
% 2.01/0.63  fof(f90,plain,(
% 2.01/0.63    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f19])).
% 2.01/0.63  fof(f19,axiom,(
% 2.01/0.63    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.01/0.63  fof(f564,plain,(
% 2.01/0.63    k1_tops_1(sK0,sK3) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3) | (~spl5_5 | ~spl5_6)),
% 2.01/0.63    inference(forward_demodulation,[],[f563,f553])).
% 2.01/0.63  fof(f553,plain,(
% 2.01/0.63    k1_tops_1(sK0,sK3) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK3)) | (~spl5_5 | ~spl5_6)),
% 2.01/0.63    inference(backward_demodulation,[],[f278,f551])).
% 2.01/0.63  fof(f551,plain,(
% 2.01/0.63    k4_xboole_0(k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK3)) | (~spl5_5 | ~spl5_6)),
% 2.01/0.63    inference(backward_demodulation,[],[f262,f531])).
% 2.01/0.63  fof(f531,plain,(
% 2.01/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f437,f123])).
% 2.01/0.63  fof(f123,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f57])).
% 2.01/0.63  fof(f57,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.01/0.63    inference(ennf_transformation,[],[f21])).
% 2.01/0.63  fof(f21,axiom,(
% 2.01/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.01/0.63  fof(f262,plain,(
% 2.01/0.63    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3)) | (~spl5_5 | ~spl5_6)),
% 2.01/0.63    inference(backward_demodulation,[],[f212,f246])).
% 2.01/0.63  fof(f212,plain,(
% 2.01/0.63    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK3)) | (~spl5_5 | ~spl5_6)),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f83,f168,f173,f102])).
% 2.01/0.63  fof(f102,plain,(
% 2.01/0.63    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f42])).
% 2.01/0.63  fof(f42,plain,(
% 2.01/0.63    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0)) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.63    inference(flattening,[],[f41])).
% 2.01/0.63  fof(f41,plain,(
% 2.01/0.63    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0))) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.63    inference(ennf_transformation,[],[f27])).
% 2.01/0.63  fof(f27,axiom,(
% 2.01/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).
% 2.01/0.63  fof(f168,plain,(
% 2.01/0.63    v3_pre_topc(sK3,sK0) | ~spl5_5),
% 2.01/0.63    inference(avatar_component_clause,[],[f166])).
% 2.01/0.63  fof(f166,plain,(
% 2.01/0.63    spl5_5 <=> v3_pre_topc(sK3,sK0)),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.01/0.63  fof(f278,plain,(
% 2.01/0.63    k1_tops_1(sK0,sK3) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK3))) | ~spl5_6),
% 2.01/0.63    inference(backward_demodulation,[],[f244,f246])).
% 2.01/0.63  fof(f244,plain,(
% 2.01/0.63    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3))) | ~spl5_6),
% 2.01/0.63    inference(forward_demodulation,[],[f211,f216])).
% 2.01/0.63  fof(f216,plain,(
% 2.01/0.63    k3_subset_1(u1_struct_0(sK0),sK3) = k4_xboole_0(u1_struct_0(sK0),sK3) | ~spl5_6),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f173,f113])).
% 2.01/0.63  fof(f211,plain,(
% 2.01/0.63    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) | ~spl5_6),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f83,f173,f101])).
% 2.01/0.63  fof(f101,plain,(
% 2.01/0.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f40])).
% 2.01/0.63  fof(f40,plain,(
% 2.01/0.63    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.63    inference(ennf_transformation,[],[f28])).
% 2.01/0.63  fof(f28,axiom,(
% 2.01/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 2.01/0.63  fof(f563,plain,(
% 2.01/0.63    k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK3)) | ~spl5_6),
% 2.01/0.63    inference(forward_demodulation,[],[f525,f531])).
% 2.01/0.63  fof(f525,plain,(
% 2.01/0.63    k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3) | ~spl5_6),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f245,f437,f114])).
% 2.01/0.63  fof(f114,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f50])).
% 2.01/0.63  fof(f50,plain,(
% 2.01/0.63    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.01/0.63    inference(ennf_transformation,[],[f22])).
% 2.01/0.63  fof(f22,axiom,(
% 2.01/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).
% 2.01/0.63  fof(f245,plain,(
% 2.01/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_6),
% 2.01/0.63    inference(subsumption_resolution,[],[f232,f175])).
% 2.01/0.63  fof(f232,plain,(
% 2.01/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | ~spl5_6),
% 2.01/0.63    inference(superposition,[],[f173,f98])).
% 2.01/0.63  fof(f473,plain,(
% 2.01/0.63    ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | (spl5_1 | ~spl5_4 | ~spl5_6)),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f150,f213,f117])).
% 2.01/0.63  fof(f117,plain,(
% 2.01/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f78])).
% 2.01/0.63  fof(f78,plain,(
% 2.01/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.01/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f76,f77])).
% 2.01/0.63  fof(f77,plain,(
% 2.01/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.01/0.63    introduced(choice_axiom,[])).
% 2.01/0.63  fof(f76,plain,(
% 2.01/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.01/0.63    inference(rectify,[],[f75])).
% 2.01/0.63  fof(f75,plain,(
% 2.01/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.01/0.63    inference(nnf_transformation,[],[f55])).
% 2.01/0.63  fof(f55,plain,(
% 2.01/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.01/0.63    inference(ennf_transformation,[],[f1])).
% 2.01/0.63  fof(f1,axiom,(
% 2.01/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.01/0.63  fof(f213,plain,(
% 2.01/0.63    r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) | (~spl5_4 | ~spl5_6)),
% 2.01/0.63    inference(unit_resulting_resolution,[],[f83,f163,f84,f173,f104])).
% 2.01/0.63  fof(f104,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f44])).
% 2.01/0.63  fof(f44,plain,(
% 2.01/0.63    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.63    inference(flattening,[],[f43])).
% 2.01/0.63  fof(f43,plain,(
% 2.01/0.63    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.63    inference(ennf_transformation,[],[f32])).
% 2.01/0.63  fof(f32,axiom,(
% 2.01/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 2.01/0.63  fof(f163,plain,(
% 2.01/0.63    r1_tarski(sK3,sK2) | ~spl5_4),
% 2.01/0.63    inference(avatar_component_clause,[],[f161])).
% 2.01/0.63  fof(f161,plain,(
% 2.01/0.63    spl5_4 <=> r1_tarski(sK3,sK2)),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.01/0.63  fof(f150,plain,(
% 2.01/0.63    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl5_1),
% 2.01/0.63    inference(avatar_component_clause,[],[f148])).
% 2.01/0.63  fof(f174,plain,(
% 2.01/0.63    spl5_1 | spl5_6),
% 2.01/0.63    inference(avatar_split_clause,[],[f85,f171,f148])).
% 2.01/0.63  fof(f85,plain,(
% 2.01/0.63    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.01/0.63    inference(cnf_transformation,[],[f73])).
% 2.01/0.63  fof(f169,plain,(
% 2.01/0.63    spl5_1 | spl5_5),
% 2.01/0.63    inference(avatar_split_clause,[],[f86,f166,f148])).
% 2.01/0.63  fof(f86,plain,(
% 2.01/0.63    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.01/0.63    inference(cnf_transformation,[],[f73])).
% 2.01/0.63  fof(f164,plain,(
% 2.01/0.63    spl5_1 | spl5_4),
% 2.01/0.63    inference(avatar_split_clause,[],[f87,f161,f148])).
% 2.01/0.63  fof(f87,plain,(
% 2.01/0.63    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.01/0.63    inference(cnf_transformation,[],[f73])).
% 2.01/0.63  fof(f159,plain,(
% 2.01/0.63    spl5_1 | spl5_3),
% 2.01/0.63    inference(avatar_split_clause,[],[f88,f156,f148])).
% 2.01/0.63  fof(f88,plain,(
% 2.01/0.63    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.01/0.63    inference(cnf_transformation,[],[f73])).
% 2.01/0.63  fof(f154,plain,(
% 2.01/0.63    ~spl5_1 | spl5_2),
% 2.01/0.63    inference(avatar_split_clause,[],[f89,f152,f148])).
% 2.01/0.63  fof(f89,plain,(
% 2.01/0.63    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f73])).
% 2.01/0.63  % SZS output end Proof for theBenchmark
% 2.01/0.63  % (8245)------------------------------
% 2.01/0.63  % (8245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.63  % (8245)Termination reason: Refutation
% 2.01/0.63  
% 2.01/0.63  % (8245)Memory used [KB]: 11129
% 2.01/0.63  % (8245)Time elapsed: 0.209 s
% 2.01/0.63  % (8245)------------------------------
% 2.01/0.63  % (8245)------------------------------
% 2.01/0.63  % (8218)Success in time 0.269 s
%------------------------------------------------------------------------------
