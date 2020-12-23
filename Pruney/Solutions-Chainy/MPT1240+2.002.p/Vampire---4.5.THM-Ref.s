%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:15 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  186 (1254 expanded)
%              Number of leaves         :   41 ( 386 expanded)
%              Depth                    :   28
%              Number of atoms          :  595 (7706 expanded)
%              Number of equality atoms :   95 ( 408 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f743,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f145,f150,f155,f160,f698,f740])).

fof(f740,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f739])).

fof(f739,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f715,f246])).

fof(f246,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f177,f241])).

fof(f241,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f161,f95])).

fof(f95,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f161,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f81,f96])).

fof(f96,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f67,f70,f69,f68])).

fof(f68,plain,
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

fof(f69,plain,
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

fof(f70,plain,
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

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f35])).

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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
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
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(f177,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f81,f82,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f71])).

fof(f715,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f172,f176,f135,f708])).

fof(f708,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK0)
        | ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X3,sK2) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f139,f241])).

fof(f139,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_2
  <=> ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f135,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_1
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f176,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f80,f81,f82,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f172,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f81,f82,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f698,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f697])).

fof(f697,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f665,f144])).

fof(f144,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f665,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f457,f658])).

fof(f658,plain,
    ( sK3 = k1_tops_1(sK0,sK3)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f637,f333])).

fof(f333,plain,
    ( sK3 = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3)
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f264,f327])).

fof(f327,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f89,f92,f290,f127])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f290,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f289,f284])).

fof(f284,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f282,f128])).

fof(f128,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f91,f102])).

fof(f102,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f282,plain,(
    k1_tops_1(sK0,k1_xboole_0) = k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f162,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f109,f102])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f162,plain,(
    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f90,f81,f97])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f289,plain,(
    ! [X0] : r1_xboole_0(k1_tops_1(sK0,k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f277,f93])).

fof(f93,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f277,plain,(
    ! [X0] : r1_xboole_0(k1_tops_1(sK0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f162,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f92,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f89,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f264,plain,
    ( k2_xboole_0(k1_xboole_0,sK3) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3)
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f223,f241])).

fof(f223,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK3) = k2_xboole_0(k1_xboole_0,sK3)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f90,f159,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f159,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f637,plain,
    ( k1_tops_1(sK0,sK3) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f623,f631])).

fof(f631,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f573,f334])).

fof(f334,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f330,f327])).

fof(f330,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) ),
    inference(unit_resulting_resolution,[],[f290,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f573,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f413,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f413,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f88,f409,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f409,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f348,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f348,plain,(
    ! [X0] : ~ r1_xboole_0(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f130,f94,f335,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f335,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f132,f334])).

fof(f132,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f120])).

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
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f94,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f130,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f88,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f623,plain,
    ( k1_tops_1(sK0,sK3) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f622,f610])).

fof(f610,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK3))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f273,f608])).

fof(f608,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK3))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f257,f586])).

fof(f586,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f413,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f257,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f205,f241])).

fof(f205,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK3))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f81,f154,f159,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v2_pre_topc(X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_pre_topc)).

fof(f154,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl5_5
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f273,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK3)))
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f239,f241])).

fof(f239,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3)))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f204,f211])).

fof(f211,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK3) = k4_xboole_0(u1_struct_0(sK0),sK3)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f159,f110])).

fof(f204,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f81,f159,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f622,plain,
    ( k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK3))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f579,f586])).

fof(f579,plain,
    ( k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f240,f413,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f240,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f227,f161])).

fof(f227,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(superposition,[],[f159,f95])).

fof(f457,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f136,f206,f117])).

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
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
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

fof(f206,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f81,f149,f82,f159,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f149,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl5_4
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f136,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f160,plain,
    ( spl5_1
    | spl5_6 ),
    inference(avatar_split_clause,[],[f83,f157,f134])).

fof(f83,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f71])).

fof(f155,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f84,f152,f134])).

fof(f84,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f71])).

fof(f150,plain,
    ( spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f85,f147,f134])).

fof(f85,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f71])).

fof(f145,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f86,f142,f134])).

fof(f86,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f71])).

fof(f140,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f87,f138,f134])).

fof(f87,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:44:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (24534)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (24531)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (24526)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (24527)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (24537)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (24532)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (24544)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (24530)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (24540)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (24528)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (24533)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (24549)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (24546)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (24529)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (24542)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (24541)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (24551)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (24554)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (24555)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (24548)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.54  % (24552)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.54  % (24550)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.54  % (24538)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (24535)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (24545)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.54  % (24547)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.54  % (24543)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.54  % (24553)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.55  % (24536)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (24539)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.49/0.59  % (24552)Refutation found. Thanks to Tanya!
% 1.49/0.59  % SZS status Theorem for theBenchmark
% 1.49/0.59  % SZS output start Proof for theBenchmark
% 1.49/0.59  fof(f743,plain,(
% 1.49/0.59    $false),
% 1.49/0.59    inference(avatar_sat_refutation,[],[f140,f145,f150,f155,f160,f698,f740])).
% 1.49/0.59  fof(f740,plain,(
% 1.49/0.59    ~spl5_1 | ~spl5_2),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f739])).
% 1.49/0.59  fof(f739,plain,(
% 1.49/0.59    $false | (~spl5_1 | ~spl5_2)),
% 1.49/0.59    inference(subsumption_resolution,[],[f715,f246])).
% 1.49/0.59  fof(f246,plain,(
% 1.49/0.59    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.49/0.59    inference(backward_demodulation,[],[f177,f241])).
% 1.49/0.59  fof(f241,plain,(
% 1.49/0.59    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f161,f95])).
% 1.49/0.59  fof(f95,plain,(
% 1.49/0.59    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f36])).
% 1.49/0.59  fof(f36,plain,(
% 1.49/0.59    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f24])).
% 1.49/0.59  fof(f24,axiom,(
% 1.49/0.59    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.49/0.59  fof(f161,plain,(
% 1.49/0.59    l1_struct_0(sK0)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f81,f96])).
% 1.49/0.59  fof(f96,plain,(
% 1.49/0.59    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f37])).
% 1.49/0.59  fof(f37,plain,(
% 1.49/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f25])).
% 1.49/0.59  fof(f25,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.49/0.59  fof(f81,plain,(
% 1.49/0.59    l1_pre_topc(sK0)),
% 1.49/0.59    inference(cnf_transformation,[],[f71])).
% 1.49/0.59  fof(f71,plain,(
% 1.49/0.59    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.49/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f67,f70,f69,f68])).
% 1.49/0.59  fof(f68,plain,(
% 1.49/0.59    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.49/0.59  fof(f69,plain,(
% 1.49/0.59    ? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.49/0.59  fof(f70,plain,(
% 1.49/0.59    ? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.49/0.59  fof(f67,plain,(
% 1.49/0.59    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.49/0.59    inference(rectify,[],[f66])).
% 1.49/0.59  fof(f66,plain,(
% 1.49/0.59    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.49/0.59    inference(flattening,[],[f65])).
% 1.49/0.59  fof(f65,plain,(
% 1.49/0.59    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.49/0.59    inference(nnf_transformation,[],[f35])).
% 1.49/0.59  fof(f35,plain,(
% 1.49/0.59    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.49/0.59    inference(flattening,[],[f34])).
% 1.49/0.59  fof(f34,plain,(
% 1.49/0.59    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f33])).
% 1.49/0.59  fof(f33,negated_conjecture,(
% 1.49/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.49/0.59    inference(negated_conjecture,[],[f32])).
% 1.49/0.59  fof(f32,conjecture,(
% 1.49/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).
% 1.49/0.59  fof(f177,plain,(
% 1.49/0.59    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f81,f82,f113])).
% 1.49/0.59  fof(f113,plain,(
% 1.49/0.59    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f53])).
% 1.49/0.59  fof(f53,plain,(
% 1.49/0.59    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(flattening,[],[f52])).
% 1.49/0.59  fof(f52,plain,(
% 1.49/0.59    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f28])).
% 1.49/0.59  fof(f28,axiom,(
% 1.49/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.49/0.59  fof(f82,plain,(
% 1.49/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.59    inference(cnf_transformation,[],[f71])).
% 1.49/0.59  fof(f715,plain,(
% 1.49/0.59    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl5_1 | ~spl5_2)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f172,f176,f135,f708])).
% 1.49/0.59  fof(f708,plain,(
% 1.49/0.59    ( ! [X3] : (~v3_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,sK2)) ) | ~spl5_2),
% 1.49/0.59    inference(forward_demodulation,[],[f139,f241])).
% 1.49/0.59  fof(f139,plain,(
% 1.49/0.59    ( ! [X3] : (~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2)) ) | ~spl5_2),
% 1.49/0.59    inference(avatar_component_clause,[],[f138])).
% 1.49/0.59  fof(f138,plain,(
% 1.49/0.59    spl5_2 <=> ! [X3] : (~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2))),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.49/0.59  fof(f135,plain,(
% 1.49/0.59    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl5_1),
% 1.49/0.59    inference(avatar_component_clause,[],[f134])).
% 1.49/0.59  fof(f134,plain,(
% 1.49/0.59    spl5_1 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.49/0.59  fof(f176,plain,(
% 1.49/0.59    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f80,f81,f82,f112])).
% 1.49/0.59  fof(f112,plain,(
% 1.49/0.59    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f51])).
% 1.49/0.59  fof(f51,plain,(
% 1.49/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.49/0.59    inference(flattening,[],[f50])).
% 1.49/0.59  fof(f50,plain,(
% 1.49/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f29])).
% 1.49/0.59  fof(f29,axiom,(
% 1.49/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.49/0.59  fof(f80,plain,(
% 1.49/0.59    v2_pre_topc(sK0)),
% 1.49/0.59    inference(cnf_transformation,[],[f71])).
% 1.49/0.59  fof(f172,plain,(
% 1.49/0.59    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f81,f82,f97])).
% 1.49/0.59  fof(f97,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f38])).
% 1.49/0.59  fof(f38,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f30])).
% 1.49/0.59  fof(f30,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.49/0.59  fof(f698,plain,(
% 1.49/0.59    spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f697])).
% 1.49/0.59  fof(f697,plain,(
% 1.49/0.59    $false | (spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 1.49/0.59    inference(subsumption_resolution,[],[f665,f144])).
% 1.49/0.59  fof(f144,plain,(
% 1.49/0.59    r2_hidden(sK1,sK3) | ~spl5_3),
% 1.49/0.59    inference(avatar_component_clause,[],[f142])).
% 1.49/0.59  fof(f142,plain,(
% 1.49/0.59    spl5_3 <=> r2_hidden(sK1,sK3)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.49/0.59  fof(f665,plain,(
% 1.49/0.59    ~r2_hidden(sK1,sK3) | (spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 1.49/0.59    inference(backward_demodulation,[],[f457,f658])).
% 1.49/0.59  fof(f658,plain,(
% 1.49/0.59    sK3 = k1_tops_1(sK0,sK3) | (~spl5_5 | ~spl5_6)),
% 1.49/0.59    inference(forward_demodulation,[],[f637,f333])).
% 1.49/0.59  fof(f333,plain,(
% 1.49/0.59    sK3 = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3) | ~spl5_6),
% 1.49/0.59    inference(backward_demodulation,[],[f264,f327])).
% 1.49/0.59  fof(f327,plain,(
% 1.49/0.59    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f89,f92,f290,f127])).
% 1.49/0.59  fof(f127,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f64])).
% 1.49/0.59  fof(f64,plain,(
% 1.49/0.59    ! [X0,X1,X2,X3] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3))),
% 1.49/0.59    inference(flattening,[],[f63])).
% 1.49/0.59  fof(f63,plain,(
% 1.49/0.59    ! [X0,X1,X2,X3] : (X1 = X2 | (~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)))),
% 1.49/0.59    inference(ennf_transformation,[],[f10])).
% 1.49/0.59  fof(f10,axiom,(
% 1.49/0.59    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.49/0.59  fof(f290,plain,(
% 1.49/0.59    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.49/0.59    inference(forward_demodulation,[],[f289,f284])).
% 1.49/0.59  fof(f284,plain,(
% 1.49/0.59    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 1.49/0.59    inference(forward_demodulation,[],[f282,f128])).
% 1.49/0.59  fof(f128,plain,(
% 1.49/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.49/0.59    inference(definition_unfolding,[],[f91,f102])).
% 1.49/0.59  fof(f102,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f7])).
% 1.49/0.59  fof(f7,axiom,(
% 1.49/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.49/0.59  fof(f91,plain,(
% 1.49/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f5])).
% 1.49/0.59  fof(f5,axiom,(
% 1.49/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.49/0.59  fof(f282,plain,(
% 1.49/0.59    k1_tops_1(sK0,k1_xboole_0) = k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0))),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f162,f129])).
% 1.49/0.59  fof(f129,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(definition_unfolding,[],[f109,f102])).
% 1.49/0.59  fof(f109,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f47])).
% 1.49/0.59  fof(f47,plain,(
% 1.49/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f4])).
% 1.49/0.59  fof(f4,axiom,(
% 1.49/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.49/0.59  fof(f162,plain,(
% 1.49/0.59    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f90,f81,f97])).
% 1.49/0.59  fof(f90,plain,(
% 1.49/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f22])).
% 1.49/0.59  fof(f22,axiom,(
% 1.49/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.49/0.59  fof(f289,plain,(
% 1.49/0.59    ( ! [X0] : (r1_xboole_0(k1_tops_1(sK0,k1_xboole_0),X0)) )),
% 1.49/0.59    inference(forward_demodulation,[],[f277,f93])).
% 1.49/0.59  fof(f93,plain,(
% 1.49/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.59    inference(cnf_transformation,[],[f6])).
% 1.49/0.59  fof(f6,axiom,(
% 1.49/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.49/0.59  fof(f277,plain,(
% 1.49/0.59    ( ! [X0] : (r1_xboole_0(k1_tops_1(sK0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) )),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f162,f122])).
% 1.49/0.59  fof(f122,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f55])).
% 1.49/0.59  fof(f55,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f11])).
% 1.49/0.59  fof(f11,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.49/0.59  fof(f92,plain,(
% 1.49/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.59    inference(cnf_transformation,[],[f3])).
% 1.49/0.59  fof(f3,axiom,(
% 1.49/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.49/0.59  fof(f89,plain,(
% 1.49/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f8])).
% 1.49/0.59  fof(f8,axiom,(
% 1.49/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.49/0.59  fof(f264,plain,(
% 1.49/0.59    k2_xboole_0(k1_xboole_0,sK3) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3) | ~spl5_6),
% 1.49/0.59    inference(backward_demodulation,[],[f223,f241])).
% 1.49/0.59  fof(f223,plain,(
% 1.49/0.59    k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK3) = k2_xboole_0(k1_xboole_0,sK3) | ~spl5_6),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f90,f159,f126])).
% 1.49/0.59  fof(f126,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f62])).
% 1.49/0.59  fof(f62,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.59    inference(flattening,[],[f61])).
% 1.49/0.59  fof(f61,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.49/0.59    inference(ennf_transformation,[],[f19])).
% 1.49/0.59  fof(f19,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.49/0.59  fof(f159,plain,(
% 1.49/0.59    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_6),
% 1.49/0.59    inference(avatar_component_clause,[],[f157])).
% 1.49/0.59  fof(f157,plain,(
% 1.49/0.59    spl5_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.49/0.59  fof(f637,plain,(
% 1.49/0.59    k1_tops_1(sK0,sK3) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK3) | (~spl5_5 | ~spl5_6)),
% 1.49/0.59    inference(backward_demodulation,[],[f623,f631])).
% 1.49/0.59  fof(f631,plain,(
% 1.49/0.59    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.49/0.59    inference(forward_demodulation,[],[f573,f334])).
% 1.49/0.59  fof(f334,plain,(
% 1.49/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.49/0.59    inference(backward_demodulation,[],[f330,f327])).
% 1.49/0.59  fof(f330,plain,(
% 1.49/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0)) )),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f290,f108])).
% 1.49/0.59  fof(f108,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f46])).
% 1.49/0.59  fof(f46,plain,(
% 1.49/0.59    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f12])).
% 1.49/0.59  fof(f12,axiom,(
% 1.49/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 1.49/0.59  fof(f573,plain,(
% 1.49/0.59    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f413,f110])).
% 1.49/0.59  fof(f110,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f48])).
% 1.49/0.59  fof(f48,plain,(
% 1.49/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f17])).
% 1.49/0.59  fof(f17,axiom,(
% 1.49/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.49/0.59  fof(f413,plain,(
% 1.49/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f88,f409,f104])).
% 1.49/0.59  fof(f104,plain,(
% 1.49/0.59    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f72])).
% 1.49/0.59  fof(f72,plain,(
% 1.49/0.59    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.49/0.59    inference(nnf_transformation,[],[f44])).
% 1.49/0.59  fof(f44,plain,(
% 1.49/0.59    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f16])).
% 1.49/0.59  fof(f16,axiom,(
% 1.49/0.59    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.49/0.59  fof(f409,plain,(
% 1.49/0.59    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f348,f107])).
% 1.49/0.59  fof(f107,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f45])).
% 1.49/0.59  fof(f45,plain,(
% 1.49/0.59    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f13])).
% 1.49/0.59  fof(f13,axiom,(
% 1.49/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.49/0.59  fof(f348,plain,(
% 1.49/0.59    ( ! [X0] : (~r1_xboole_0(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f130,f94,f335,f125])).
% 1.49/0.59  fof(f125,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f60])).
% 1.49/0.59  fof(f60,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.49/0.59    inference(flattening,[],[f59])).
% 1.49/0.59  fof(f59,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.49/0.59    inference(ennf_transformation,[],[f9])).
% 1.49/0.59  fof(f9,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 1.49/0.59  fof(f335,plain,(
% 1.49/0.59    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 1.49/0.59    inference(backward_demodulation,[],[f132,f334])).
% 1.49/0.59  fof(f132,plain,(
% 1.49/0.59    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.49/0.59    inference(equality_resolution,[],[f120])).
% 1.49/0.59  fof(f120,plain,(
% 1.49/0.59    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f79])).
% 1.49/0.59  fof(f79,plain,(
% 1.49/0.59    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.49/0.59    inference(nnf_transformation,[],[f14])).
% 1.49/0.59  fof(f14,axiom,(
% 1.49/0.59    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.49/0.59  fof(f94,plain,(
% 1.49/0.59    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f15])).
% 1.49/0.59  fof(f15,axiom,(
% 1.49/0.59    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 1.49/0.59  fof(f130,plain,(
% 1.49/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.49/0.59    inference(equality_resolution,[],[f115])).
% 1.49/0.59  fof(f115,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.49/0.59    inference(cnf_transformation,[],[f74])).
% 1.49/0.59  fof(f74,plain,(
% 1.49/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.59    inference(flattening,[],[f73])).
% 1.49/0.59  fof(f73,plain,(
% 1.49/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.59    inference(nnf_transformation,[],[f2])).
% 1.49/0.59  fof(f2,axiom,(
% 1.49/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.59  fof(f88,plain,(
% 1.49/0.59    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f18])).
% 1.49/0.59  fof(f18,axiom,(
% 1.49/0.59    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.49/0.59  fof(f623,plain,(
% 1.49/0.59    k1_tops_1(sK0,sK3) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3) | (~spl5_5 | ~spl5_6)),
% 1.49/0.59    inference(forward_demodulation,[],[f622,f610])).
% 1.49/0.59  fof(f610,plain,(
% 1.49/0.59    k1_tops_1(sK0,sK3) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK3)) | (~spl5_5 | ~spl5_6)),
% 1.49/0.59    inference(backward_demodulation,[],[f273,f608])).
% 1.49/0.59  fof(f608,plain,(
% 1.49/0.59    k4_xboole_0(k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK3)) | (~spl5_5 | ~spl5_6)),
% 1.49/0.59    inference(backward_demodulation,[],[f257,f586])).
% 1.49/0.59  fof(f586,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f413,f123])).
% 1.49/0.59  fof(f123,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f56])).
% 1.49/0.59  fof(f56,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f20])).
% 1.49/0.59  fof(f20,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.49/0.59  fof(f257,plain,(
% 1.49/0.59    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3)) | (~spl5_5 | ~spl5_6)),
% 1.49/0.59    inference(backward_demodulation,[],[f205,f241])).
% 1.49/0.59  fof(f205,plain,(
% 1.49/0.59    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK3) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK3)) | (~spl5_5 | ~spl5_6)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f81,f154,f159,f99])).
% 1.49/0.59  fof(f99,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f41])).
% 1.49/0.59  fof(f41,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0)) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(flattening,[],[f40])).
% 1.49/0.59  fof(f40,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0))) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f26])).
% 1.49/0.59  fof(f26,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_pre_topc)).
% 1.49/0.59  fof(f154,plain,(
% 1.49/0.59    v3_pre_topc(sK3,sK0) | ~spl5_5),
% 1.49/0.59    inference(avatar_component_clause,[],[f152])).
% 1.49/0.59  fof(f152,plain,(
% 1.49/0.59    spl5_5 <=> v3_pre_topc(sK3,sK0)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.49/0.59  fof(f273,plain,(
% 1.49/0.59    k1_tops_1(sK0,sK3) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK3))) | ~spl5_6),
% 1.49/0.59    inference(backward_demodulation,[],[f239,f241])).
% 1.49/0.59  fof(f239,plain,(
% 1.49/0.59    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK3))) | ~spl5_6),
% 1.49/0.59    inference(forward_demodulation,[],[f204,f211])).
% 1.49/0.59  fof(f211,plain,(
% 1.49/0.59    k3_subset_1(u1_struct_0(sK0),sK3) = k4_xboole_0(u1_struct_0(sK0),sK3) | ~spl5_6),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f159,f110])).
% 1.49/0.59  fof(f204,plain,(
% 1.49/0.59    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) | ~spl5_6),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f81,f159,f98])).
% 1.49/0.59  fof(f98,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f39])).
% 1.49/0.59  fof(f39,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f27])).
% 1.49/0.59  fof(f27,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.49/0.59  fof(f622,plain,(
% 1.49/0.59    k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK3)) | ~spl5_6),
% 1.49/0.59    inference(forward_demodulation,[],[f579,f586])).
% 1.49/0.59  fof(f579,plain,(
% 1.49/0.59    k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK3)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK3) | ~spl5_6),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f240,f413,f111])).
% 1.49/0.59  fof(f111,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f49])).
% 1.49/0.59  fof(f49,plain,(
% 1.49/0.59    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f21])).
% 1.49/0.59  fof(f21,axiom,(
% 1.49/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 1.49/0.59  fof(f240,plain,(
% 1.49/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_6),
% 1.49/0.59    inference(subsumption_resolution,[],[f227,f161])).
% 1.49/0.59  fof(f227,plain,(
% 1.49/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | ~spl5_6),
% 1.49/0.59    inference(superposition,[],[f159,f95])).
% 1.49/0.59  fof(f457,plain,(
% 1.49/0.59    ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | (spl5_1 | ~spl5_4 | ~spl5_6)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f136,f206,f117])).
% 1.49/0.59  fof(f117,plain,(
% 1.49/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f78])).
% 1.49/0.59  fof(f78,plain,(
% 1.49/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f76,f77])).
% 1.49/0.59  fof(f77,plain,(
% 1.49/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.49/0.59  fof(f76,plain,(
% 1.49/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.59    inference(rectify,[],[f75])).
% 1.49/0.59  fof(f75,plain,(
% 1.49/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.59    inference(nnf_transformation,[],[f54])).
% 1.49/0.59  fof(f54,plain,(
% 1.49/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f1])).
% 1.49/0.59  fof(f1,axiom,(
% 1.49/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.49/0.59  fof(f206,plain,(
% 1.49/0.59    r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) | (~spl5_4 | ~spl5_6)),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f81,f149,f82,f159,f101])).
% 1.49/0.59  fof(f101,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f43])).
% 1.49/0.59  fof(f43,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(flattening,[],[f42])).
% 1.49/0.59  fof(f42,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f31])).
% 1.49/0.59  fof(f31,axiom,(
% 1.49/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.49/0.59  fof(f149,plain,(
% 1.49/0.59    r1_tarski(sK3,sK2) | ~spl5_4),
% 1.49/0.59    inference(avatar_component_clause,[],[f147])).
% 1.49/0.59  fof(f147,plain,(
% 1.49/0.59    spl5_4 <=> r1_tarski(sK3,sK2)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.49/0.59  fof(f136,plain,(
% 1.49/0.59    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl5_1),
% 1.49/0.59    inference(avatar_component_clause,[],[f134])).
% 1.49/0.59  fof(f160,plain,(
% 1.49/0.59    spl5_1 | spl5_6),
% 1.49/0.59    inference(avatar_split_clause,[],[f83,f157,f134])).
% 1.49/0.59  fof(f83,plain,(
% 1.49/0.59    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.49/0.59    inference(cnf_transformation,[],[f71])).
% 1.49/0.59  fof(f155,plain,(
% 1.49/0.59    spl5_1 | spl5_5),
% 1.49/0.59    inference(avatar_split_clause,[],[f84,f152,f134])).
% 1.49/0.59  fof(f84,plain,(
% 1.49/0.59    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.49/0.59    inference(cnf_transformation,[],[f71])).
% 1.49/0.59  fof(f150,plain,(
% 1.49/0.59    spl5_1 | spl5_4),
% 1.49/0.59    inference(avatar_split_clause,[],[f85,f147,f134])).
% 1.49/0.59  fof(f85,plain,(
% 1.49/0.59    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.49/0.59    inference(cnf_transformation,[],[f71])).
% 1.49/0.59  fof(f145,plain,(
% 1.49/0.59    spl5_1 | spl5_3),
% 1.49/0.59    inference(avatar_split_clause,[],[f86,f142,f134])).
% 1.49/0.59  fof(f86,plain,(
% 1.49/0.59    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.49/0.59    inference(cnf_transformation,[],[f71])).
% 1.49/0.59  fof(f140,plain,(
% 1.49/0.59    ~spl5_1 | spl5_2),
% 1.49/0.59    inference(avatar_split_clause,[],[f87,f138,f134])).
% 1.49/0.59  fof(f87,plain,(
% 1.49/0.59    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 1.49/0.59    inference(cnf_transformation,[],[f71])).
% 1.49/0.59  % SZS output end Proof for theBenchmark
% 1.49/0.59  % (24552)------------------------------
% 1.49/0.59  % (24552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (24552)Termination reason: Refutation
% 1.49/0.59  
% 1.49/0.59  % (24552)Memory used [KB]: 11129
% 1.49/0.59  % (24552)Time elapsed: 0.179 s
% 1.49/0.59  % (24552)------------------------------
% 1.49/0.59  % (24552)------------------------------
% 1.49/0.60  % (24525)Success in time 0.238 s
%------------------------------------------------------------------------------
