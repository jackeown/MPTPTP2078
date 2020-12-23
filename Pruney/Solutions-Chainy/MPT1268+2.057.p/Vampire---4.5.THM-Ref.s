%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 322 expanded)
%              Number of leaves         :   21 ( 102 expanded)
%              Depth                    :   21
%              Number of atoms          :  514 (2949 expanded)
%              Number of equality atoms :   53 ( 433 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f87,f163,f252])).

fof(f252,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f250,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f250,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(sK2))
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f244,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f244,plain,
    ( r2_hidden(sK4(sK2),k1_xboole_0)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f243,f69])).

fof(f69,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f243,plain,
    ( r2_hidden(sK4(sK2),k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f210,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f210,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | r2_hidden(X2,k1_xboole_0) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f209,f171])).

fof(f171,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f170,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_tops_1(X1,sK0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK0)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK0)
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_tops_1(sK1,sK0) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK0)
            | ~ r1_tarski(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK0)
        & r1_tarski(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK2
      & v3_pre_topc(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(f170,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f114,f83])).

fof(f83,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f114,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f209,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f206,f77])).

fof(f77,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f206,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK2,sK1)
        | r2_hidden(X2,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(resolution,[],[f186,f41])).

% (6319)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X1)
        | r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f185,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r1_tarski(sK2,X1)
        | r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f184,f40])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r1_tarski(sK2,X1)
        | r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f179,f73])).

fof(f73,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_3
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r1_tarski(sK2,X1)
        | ~ v3_pre_topc(sK2,sK0)
        | r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f81,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ( r2_hidden(X1,sK3(X0,X1,X2))
                & r1_tarski(sK3(X0,X1,X2),X2)
                & v3_pre_topc(sK3(X0,X1,X2),X0)
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK3(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X2)
        & v3_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f81,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f163,plain,
    ( spl5_1
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f161,f40])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f160,f41])).

fof(f160,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f159,f66])).

fof(f66,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f159,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(trivial_inequality_removal,[],[f158])).

fof(f158,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(superposition,[],[f50,f147])).

fof(f147,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f145,f108])).

fof(f108,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f106,f40])).

fof(f106,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f145,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f136,f113])).

fof(f113,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f112,f39])).

fof(f112,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f110,f40])).

fof(f110,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f59,f41])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f136,plain,
    ( ! [X2] :
        ( ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1)
        | k1_xboole_0 = X2 )
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ! [X2] :
        ( k1_xboole_0 = X2
        | ~ r1_tarski(X2,sK1)
        | ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1) )
    | ~ spl5_6 ),
    inference(resolution,[],[f101,f104])).

fof(f104,plain,(
    ! [X2] :
      ( r1_tarski(X2,u1_struct_0(sK0))
      | ~ r1_tarski(X2,sK1) ) ),
    inference(resolution,[],[f63,f100])).

fof(f100,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f60,f41])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f61,f86])).

fof(f86,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_6
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,
    ( spl5_1
    | spl5_6 ),
    inference(avatar_split_clause,[],[f42,f85,f65])).

fof(f42,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f43,f80,f65])).

fof(f43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f44,f76,f65])).

fof(f44,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f45,f72,f65])).

fof(f45,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f46,f68,f65])).

fof(f46,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 10:05:11 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.46  % (6315)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (6308)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (6308)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (6323)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f87,f163,f252])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ~spl5_1 | spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f251])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    $false | (~spl5_1 | spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f250,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,sK4(sK2)) | (~spl5_1 | spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(resolution,[],[f244,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    r2_hidden(sK4(sK2),k1_xboole_0) | (~spl5_1 | spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f243,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    k1_xboole_0 != sK2 | spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl5_2 <=> k1_xboole_0 = sK2),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    r2_hidden(sK4(sK2),k1_xboole_0) | k1_xboole_0 = sK2 | (~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(resolution,[],[f210,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,sK2) | r2_hidden(X2,k1_xboole_0)) ) | (~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(forward_demodulation,[],[f209,f171])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f170,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(rectify,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f114,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    v2_tops_1(sK1,sK0) | ~spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl5_1 <=> v2_tops_1(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f49,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ( ! [X2] : (r2_hidden(X2,k1_tops_1(sK0,sK1)) | ~r2_hidden(X2,sK2)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f206,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    r1_tarski(sK2,sK1) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl5_4 <=> r1_tarski(sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_tarski(sK2,sK1) | r2_hidden(X2,k1_tops_1(sK0,sK1)) | ~r2_hidden(X2,sK2)) ) | (~spl5_3 | ~spl5_5)),
% 0.21/0.50    inference(resolution,[],[f186,f41])).
% 0.21/0.50  % (6319)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X1) | r2_hidden(X0,k1_tops_1(sK0,X1)) | ~r2_hidden(X0,sK2)) ) | (~spl5_3 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f185,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | ~r1_tarski(sK2,X1) | r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) ) | (~spl5_3 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f184,f40])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | ~r1_tarski(sK2,X1) | r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl5_3 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f179,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    v3_pre_topc(sK2,sK0) | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl5_3 <=> v3_pre_topc(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | ~r1_tarski(sK2,X1) | ~v3_pre_topc(sK2,sK0) | r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f81,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK3(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X2) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X2) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(rectify,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl5_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    spl5_1 | ~spl5_6),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    $false | (spl5_1 | ~spl5_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f161,f40])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f160,f41])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ~v2_tops_1(sK1,sK0) | spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f65])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_6),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_6),
% 0.21/0.50    inference(superposition,[],[f50,f147])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl5_6),
% 0.21/0.50    inference(subsumption_resolution,[],[f145,f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f106,f40])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f48,f41])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl5_6),
% 0.21/0.50    inference(resolution,[],[f136,f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f112,f39])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f110,f40])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f59,f41])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ( ! [X2] : (~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1) | k1_xboole_0 = X2) ) | ~spl5_6),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f132])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X2] : (k1_xboole_0 = X2 | ~r1_tarski(X2,sK1) | ~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1)) ) | ~spl5_6),
% 0.21/0.50    inference(resolution,[],[f101,f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ( ! [X2] : (r1_tarski(X2,u1_struct_0(sK0)) | ~r1_tarski(X2,sK1)) )),
% 0.21/0.50    inference(resolution,[],[f63,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(resolution,[],[f60,f41])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0)) ) | ~spl5_6),
% 0.21/0.50    inference(resolution,[],[f61,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0)) ) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl5_6 <=> ! [X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl5_1 | spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f85,f65])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ~spl5_1 | spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f80,f65])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ~spl5_1 | spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f76,f65])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~spl5_1 | spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f72,f65])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~spl5_1 | ~spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f68,f65])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (6308)------------------------------
% 0.21/0.50  % (6308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6308)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (6308)Memory used [KB]: 10746
% 0.21/0.50  % (6308)Time elapsed: 0.084 s
% 0.21/0.50  % (6308)------------------------------
% 0.21/0.50  % (6308)------------------------------
% 0.21/0.50  % (6309)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (6305)Success in time 0.143 s
%------------------------------------------------------------------------------
