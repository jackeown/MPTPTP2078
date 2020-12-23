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
% DateTime   : Thu Dec  3 13:16:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 430 expanded)
%              Number of leaves         :   28 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  472 (1961 expanded)
%              Number of equality atoms :   30 ( 129 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f306,f1413,f1414,f1809,f1811,f1813,f1844,f1859,f2153])).

fof(f2153,plain,
    ( ~ spl7_9
    | ~ spl7_11
    | spl7_32 ),
    inference(avatar_contradiction_clause,[],[f2152])).

fof(f2152,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_11
    | spl7_32 ),
    inference(subsumption_resolution,[],[f2115,f2151])).

fof(f2151,plain,
    ( r1_tarski(u1_pre_topc(sK2),k3_tarski(u1_pre_topc(sK2)))
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f2145,f55])).

fof(f55,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f2145,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(u1_pre_topc(sK2))),k3_tarski(u1_pre_topc(sK2)))
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f2137,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f2137,plain,
    ( r1_tarski(k1_zfmisc_1(u1_pre_topc(sK2)),u1_pre_topc(sK2))
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f1853,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1853,plain,
    ( m1_subset_1(k1_zfmisc_1(u1_pre_topc(sK2)),k1_zfmisc_1(u1_pre_topc(sK2)))
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f351,f351,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f351,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK2)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl7_9
  <=> v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f2115,plain,
    ( ~ r1_tarski(u1_pre_topc(sK2),k3_tarski(u1_pre_topc(sK2)))
    | ~ spl7_11
    | spl7_32 ),
    inference(unit_resulting_resolution,[],[f1886,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1886,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK2))))
    | ~ spl7_11
    | spl7_32 ),
    inference(unit_resulting_resolution,[],[f1799,f370,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f370,plain,
    ( v1_xboole_0(k1_zfmisc_1(k3_tarski(u1_pre_topc(sK2))))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl7_11
  <=> v1_xboole_0(k1_zfmisc_1(k3_tarski(u1_pre_topc(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f1799,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK2))
    | spl7_32 ),
    inference(avatar_component_clause,[],[f1798])).

fof(f1798,plain,
    ( spl7_32
  <=> v1_xboole_0(u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f1859,plain,
    ( ~ spl7_9
    | ~ spl7_32 ),
    inference(avatar_contradiction_clause,[],[f1858])).

fof(f1858,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1832,f1850])).

fof(f1850,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_pre_topc(sK2)))
    | ~ spl7_9
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f1800,f351,f82])).

fof(f1800,plain,
    ( v1_xboole_0(u1_pre_topc(sK2))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f1798])).

fof(f1832,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_pre_topc(sK2)))
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f1800,f100,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f100,plain,(
    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(unit_resulting_resolution,[],[f96,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0))
          & r2_hidden(sK4(X0),u1_pre_topc(X0))
          & r2_hidden(sK3(X0),u1_pre_topc(X0))
          & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
          & r1_tarski(sK5(X0),u1_pre_topc(X0))
          & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f43,f42,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK3(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0))
        & r2_hidden(sK4(X0),u1_pre_topc(X0))
        & r2_hidden(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
        & r1_tarski(sK5(X0),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ( ! [X1] :
            ( ! [X2] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                | ~ r2_hidden(X2,u1_pre_topc(X0))
                | ~ r2_hidden(X1,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f96,plain,(
    sP0(sK2) ),
    inference(unit_resulting_resolution,[],[f95,f52,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f52,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f95,plain,(
    sP1(sK2) ),
    inference(unit_resulting_resolution,[],[f53,f78])).

fof(f78,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f33,f32])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f1844,plain,
    ( spl7_9
    | ~ spl7_32 ),
    inference(avatar_contradiction_clause,[],[f1843])).

fof(f1843,plain,
    ( $false
    | spl7_9
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1786,f1832])).

fof(f1786,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_pre_topc(sK2)))
    | spl7_9 ),
    inference(unit_resulting_resolution,[],[f1769,f92])).

fof(f1769,plain,
    ( r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK2))
    | spl7_9 ),
    inference(unit_resulting_resolution,[],[f350,f1379])).

fof(f1379,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f1378])).

fof(f1378,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | v1_xboole_0(k1_zfmisc_1(X0))
      | r1_tarski(X0,X0) ) ),
    inference(forward_demodulation,[],[f1373,f55])).

fof(f1373,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | r1_tarski(X0,X0)
      | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) ) ),
    inference(resolution,[],[f900,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK6(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f900,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK6(k1_zfmisc_1(X0),X1),X0)
      | v1_xboole_0(k1_zfmisc_1(X0))
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f899,f55])).

fof(f899,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | r1_tarski(sK6(k1_zfmisc_1(X0),X1),X0)
      | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X1) ) ),
    inference(resolution,[],[f102,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f80,f91])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f350,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK2)))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f349])).

fof(f1813,plain,(
    ~ spl7_33 ),
    inference(avatar_contradiction_clause,[],[f1812])).

fof(f1812,plain,
    ( $false
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f54,f1804])).

fof(f1804,plain,
    ( u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f1802])).

fof(f1802,plain,
    ( spl7_33
  <=> u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f54,plain,(
    u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f1811,plain,(
    spl7_34 ),
    inference(avatar_contradiction_clause,[],[f1810])).

fof(f1810,plain,
    ( $false
    | spl7_34 ),
    inference(subsumption_resolution,[],[f100,f1808])).

fof(f1808,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl7_34 ),
    inference(avatar_component_clause,[],[f1806])).

fof(f1806,plain,
    ( spl7_34
  <=> r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f1809,plain,
    ( spl7_32
    | spl7_33
    | ~ spl7_34
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f1748,f303,f1806,f1802,f1798])).

fof(f303,plain,
    ( spl7_8
  <=> u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1748,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))
    | v1_xboole_0(u1_pre_topc(sK2))
    | ~ spl7_8 ),
    inference(superposition,[],[f56,f305])).

fof(f305,plain,
    ( u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f303])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f1414,plain,
    ( spl7_7
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f1390])).

fof(f1390,plain,
    ( $false
    | spl7_7
    | spl7_9 ),
    inference(unit_resulting_resolution,[],[f350,f333,f1379])).

fof(f333,plain,
    ( ~ r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK2))
    | spl7_7 ),
    inference(unit_resulting_resolution,[],[f315,f83])).

fof(f315,plain,
    ( ~ r1_tarski(k3_tarski(u1_pre_topc(sK2)),k3_tarski(u1_pre_topc(sK2)))
    | spl7_7 ),
    inference(unit_resulting_resolution,[],[f100,f311,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f311,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),k3_tarski(u1_pre_topc(sK2)))
    | spl7_7 ),
    inference(unit_resulting_resolution,[],[f301,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      | m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f301,plain,
    ( ~ m1_setfam_1(u1_pre_topc(sK2),u1_struct_0(sK2))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl7_7
  <=> m1_setfam_1(u1_pre_topc(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f1413,plain,
    ( spl7_7
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f1388])).

fof(f1388,plain,
    ( $false
    | spl7_7
    | spl7_11 ),
    inference(unit_resulting_resolution,[],[f369,f315,f1379])).

fof(f369,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k3_tarski(u1_pre_topc(sK2))))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f368])).

fof(f306,plain,
    ( ~ spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f297,f303,f299])).

fof(f297,plain,
    ( u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2))
    | ~ m1_setfam_1(u1_pre_topc(sK2),u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f296,f227])).

fof(f227,plain,(
    k3_tarski(u1_pre_topc(sK2)) = k5_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(unit_resulting_resolution,[],[f105,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f105,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(unit_resulting_resolution,[],[f53,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f296,plain,
    ( ~ m1_setfam_1(u1_pre_topc(sK2),u1_struct_0(sK2))
    | u1_struct_0(sK2) = k5_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(resolution,[],[f85,f105])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_setfam_1(X1,X0)
      | k5_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( m1_setfam_1(X1,X0)
          | k5_setfam_1(X0,X1) != X0 )
        & ( k5_setfam_1(X0,X1) = X0
          | ~ m1_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:57:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (9305)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (9304)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (9301)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (9300)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (9303)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (9309)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.50  % (9302)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (9323)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (9303)Refutation not found, incomplete strategy% (9303)------------------------------
% 0.21/0.50  % (9303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9315)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (9308)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (9320)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (9317)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (9311)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (9307)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (9306)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (9312)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (9319)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (9321)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (9307)Refutation not found, incomplete strategy% (9307)------------------------------
% 0.21/0.51  % (9307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9307)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9307)Memory used [KB]: 6140
% 0.21/0.51  % (9307)Time elapsed: 0.068 s
% 0.21/0.51  % (9307)------------------------------
% 0.21/0.51  % (9307)------------------------------
% 0.21/0.52  % (9306)Refutation not found, incomplete strategy% (9306)------------------------------
% 0.21/0.52  % (9306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9310)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (9303)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9303)Memory used [KB]: 10618
% 0.21/0.52  % (9303)Time elapsed: 0.094 s
% 0.21/0.52  % (9303)------------------------------
% 0.21/0.52  % (9303)------------------------------
% 0.21/0.52  % (9310)Refutation not found, incomplete strategy% (9310)------------------------------
% 0.21/0.52  % (9310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9310)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9310)Memory used [KB]: 10490
% 0.21/0.52  % (9310)Time elapsed: 0.117 s
% 0.21/0.52  % (9310)------------------------------
% 0.21/0.52  % (9310)------------------------------
% 0.21/0.52  % (9316)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (9306)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9306)Memory used [KB]: 10618
% 0.21/0.52  % (9306)Time elapsed: 0.090 s
% 0.21/0.52  % (9306)------------------------------
% 0.21/0.52  % (9306)------------------------------
% 0.21/0.52  % (9313)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % (9318)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (9308)Refutation not found, incomplete strategy% (9308)------------------------------
% 0.21/0.52  % (9308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9308)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9308)Memory used [KB]: 10490
% 0.21/0.52  % (9308)Time elapsed: 0.117 s
% 0.21/0.52  % (9308)------------------------------
% 0.21/0.52  % (9308)------------------------------
% 0.21/0.53  % (9314)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.54  % (9322)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.58  % (9314)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f2155,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f306,f1413,f1414,f1809,f1811,f1813,f1844,f1859,f2153])).
% 0.21/0.58  fof(f2153,plain,(
% 0.21/0.58    ~spl7_9 | ~spl7_11 | spl7_32),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f2152])).
% 0.21/0.58  fof(f2152,plain,(
% 0.21/0.58    $false | (~spl7_9 | ~spl7_11 | spl7_32)),
% 0.21/0.58    inference(subsumption_resolution,[],[f2115,f2151])).
% 0.21/0.58  fof(f2151,plain,(
% 0.21/0.58    r1_tarski(u1_pre_topc(sK2),k3_tarski(u1_pre_topc(sK2))) | ~spl7_9),
% 0.21/0.58    inference(forward_demodulation,[],[f2145,f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.58  fof(f2145,plain,(
% 0.21/0.58    r1_tarski(k3_tarski(k1_zfmisc_1(u1_pre_topc(sK2))),k3_tarski(u1_pre_topc(sK2))) | ~spl7_9),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f2137,f83])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.21/0.58  fof(f2137,plain,(
% 0.21/0.58    r1_tarski(k1_zfmisc_1(u1_pre_topc(sK2)),u1_pre_topc(sK2)) | ~spl7_9),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f1853,f91])).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.58    inference(nnf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.58  fof(f1853,plain,(
% 0.21/0.58    m1_subset_1(k1_zfmisc_1(u1_pre_topc(sK2)),k1_zfmisc_1(u1_pre_topc(sK2))) | ~spl7_9),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f351,f351,f82])).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~v1_xboole_0(X1) | m1_subset_1(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(nnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.58  fof(f351,plain,(
% 0.21/0.58    v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK2))) | ~spl7_9),
% 0.21/0.58    inference(avatar_component_clause,[],[f349])).
% 0.21/0.58  fof(f349,plain,(
% 0.21/0.58    spl7_9 <=> v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.58  fof(f2115,plain,(
% 0.21/0.58    ~r1_tarski(u1_pre_topc(sK2),k3_tarski(u1_pre_topc(sK2))) | (~spl7_11 | spl7_32)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f1886,f92])).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f50])).
% 0.21/0.58  fof(f1886,plain,(
% 0.21/0.58    ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK2)))) | (~spl7_11 | spl7_32)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f1799,f370,f81])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f370,plain,(
% 0.21/0.58    v1_xboole_0(k1_zfmisc_1(k3_tarski(u1_pre_topc(sK2)))) | ~spl7_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f368])).
% 0.21/0.58  fof(f368,plain,(
% 0.21/0.58    spl7_11 <=> v1_xboole_0(k1_zfmisc_1(k3_tarski(u1_pre_topc(sK2))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.58  fof(f1799,plain,(
% 0.21/0.58    ~v1_xboole_0(u1_pre_topc(sK2)) | spl7_32),
% 0.21/0.58    inference(avatar_component_clause,[],[f1798])).
% 0.21/0.58  fof(f1798,plain,(
% 0.21/0.58    spl7_32 <=> v1_xboole_0(u1_pre_topc(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.58  fof(f1859,plain,(
% 0.21/0.58    ~spl7_9 | ~spl7_32),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1858])).
% 0.21/0.58  fof(f1858,plain,(
% 0.21/0.58    $false | (~spl7_9 | ~spl7_32)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1832,f1850])).
% 0.21/0.58  fof(f1850,plain,(
% 0.21/0.58    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_pre_topc(sK2))) | (~spl7_9 | ~spl7_32)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f1800,f351,f82])).
% 0.21/0.58  fof(f1800,plain,(
% 0.21/0.58    v1_xboole_0(u1_pre_topc(sK2)) | ~spl7_32),
% 0.21/0.58    inference(avatar_component_clause,[],[f1798])).
% 0.21/0.58  fof(f1832,plain,(
% 0.21/0.58    ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_pre_topc(sK2))) | ~spl7_32),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f1800,f100,f94])).
% 0.21/0.58  fof(f94,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.58  fof(f100,plain,(
% 0.21/0.58    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f96,f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ! [X0] : ((sP0(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f43,f42,f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & r2_hidden(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ! [X0] : (? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.21/0.58    inference(rectify,[],[f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.21/0.58    inference(flattening,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ! [X0] : ((sP0(X0) | (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.21/0.58    inference(nnf_transformation,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ! [X0] : (sP0(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.21/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.58  fof(f96,plain,(
% 0.21/0.58    sP0(sK2)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f95,f52,f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X0] : (~v2_pre_topc(X0) | sP0(X0) | ~sP1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_pre_topc(X0))) | ~sP1(X0))),
% 0.21/0.58    inference(nnf_transformation,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ! [X0] : ((v2_pre_topc(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    v2_pre_topc(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,negated_conjecture,(
% 0.21/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.21/0.58    inference(negated_conjecture,[],[f14])).
% 0.21/0.58  fof(f14,conjecture,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).
% 0.21/0.58  fof(f95,plain,(
% 0.21/0.58    sP1(sK2)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f53,f78])).
% 0.21/0.58  fof(f78,plain,(
% 0.21/0.58    ( ! [X0] : (sP1(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0] : (sP1(X0) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(definition_folding,[],[f23,f33,f32])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.58    inference(rectify,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    l1_pre_topc(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f36])).
% 0.21/0.58  fof(f1844,plain,(
% 0.21/0.58    spl7_9 | ~spl7_32),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1843])).
% 0.21/0.58  fof(f1843,plain,(
% 0.21/0.58    $false | (spl7_9 | ~spl7_32)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1786,f1832])).
% 0.21/0.58  fof(f1786,plain,(
% 0.21/0.58    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(u1_pre_topc(sK2))) | spl7_9),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f1769,f92])).
% 0.21/0.58  fof(f1769,plain,(
% 0.21/0.58    r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK2)) | spl7_9),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f350,f1379])).
% 0.21/0.58  fof(f1379,plain,(
% 0.21/0.58    ( ! [X0] : (r1_tarski(X0,X0) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f1378])).
% 0.21/0.58  fof(f1378,plain,(
% 0.21/0.58    ( ! [X0] : (r1_tarski(X0,X0) | v1_xboole_0(k1_zfmisc_1(X0)) | r1_tarski(X0,X0)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f1373,f55])).
% 0.21/0.58  fof(f1373,plain,(
% 0.21/0.58    ( ! [X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | r1_tarski(X0,X0) | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0)) )),
% 0.21/0.58    inference(resolution,[],[f900,f88])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(sK6(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f47])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.21/0.58  fof(f900,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(sK6(k1_zfmisc_1(X0),X1),X0) | v1_xboole_0(k1_zfmisc_1(X0)) | r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f899,f55])).
% 0.21/0.58  fof(f899,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | r1_tarski(sK6(k1_zfmisc_1(X0),X1),X0) | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X1)) )),
% 0.21/0.58    inference(resolution,[],[f102,f87])).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f48])).
% 0.21/0.58  fof(f102,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(resolution,[],[f80,f91])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f45])).
% 0.21/0.58  fof(f350,plain,(
% 0.21/0.58    ~v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK2))) | spl7_9),
% 0.21/0.58    inference(avatar_component_clause,[],[f349])).
% 0.21/0.58  fof(f1813,plain,(
% 0.21/0.58    ~spl7_33),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1812])).
% 0.21/0.58  fof(f1812,plain,(
% 0.21/0.58    $false | ~spl7_33),
% 0.21/0.58    inference(subsumption_resolution,[],[f54,f1804])).
% 0.21/0.58  fof(f1804,plain,(
% 0.21/0.58    u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) | ~spl7_33),
% 0.21/0.58    inference(avatar_component_clause,[],[f1802])).
% 0.21/0.58  fof(f1802,plain,(
% 0.21/0.58    spl7_33 <=> u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    u1_struct_0(sK2) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2)))),
% 0.21/0.58    inference(cnf_transformation,[],[f36])).
% 0.21/0.58  fof(f1811,plain,(
% 0.21/0.58    spl7_34),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1810])).
% 0.21/0.58  fof(f1810,plain,(
% 0.21/0.58    $false | spl7_34),
% 0.21/0.58    inference(subsumption_resolution,[],[f100,f1808])).
% 0.21/0.58  fof(f1808,plain,(
% 0.21/0.58    ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) | spl7_34),
% 0.21/0.58    inference(avatar_component_clause,[],[f1806])).
% 0.21/0.58  fof(f1806,plain,(
% 0.21/0.58    spl7_34 <=> r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.58  fof(f1809,plain,(
% 0.21/0.58    spl7_32 | spl7_33 | ~spl7_34 | ~spl7_8),
% 0.21/0.58    inference(avatar_split_clause,[],[f1748,f303,f1806,f1802,f1798])).
% 0.21/0.58  fof(f303,plain,(
% 0.21/0.58    spl7_8 <=> u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.58  fof(f1748,plain,(
% 0.21/0.58    ~r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) | u1_struct_0(sK2) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK2))) | v1_xboole_0(u1_pre_topc(sK2)) | ~spl7_8),
% 0.21/0.58    inference(superposition,[],[f56,f305])).
% 0.21/0.58  fof(f305,plain,(
% 0.21/0.58    u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2)) | ~spl7_8),
% 0.21/0.58    inference(avatar_component_clause,[],[f303])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.21/0.58    inference(flattening,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.21/0.58  fof(f1414,plain,(
% 0.21/0.58    spl7_7 | spl7_9),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1390])).
% 0.21/0.58  fof(f1390,plain,(
% 0.21/0.58    $false | (spl7_7 | spl7_9)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f350,f333,f1379])).
% 0.21/0.58  fof(f333,plain,(
% 0.21/0.58    ~r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK2)) | spl7_7),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f315,f83])).
% 0.21/0.58  fof(f315,plain,(
% 0.21/0.58    ~r1_tarski(k3_tarski(u1_pre_topc(sK2)),k3_tarski(u1_pre_topc(sK2))) | spl7_7),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f100,f311,f93])).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.58    inference(flattening,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.21/0.58  fof(f311,plain,(
% 0.21/0.58    ~r1_tarski(u1_struct_0(sK2),k3_tarski(u1_pre_topc(sK2))) | spl7_7),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f301,f90])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) | m1_setfam_1(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.21/0.58    inference(nnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.21/0.58  fof(f301,plain,(
% 0.21/0.58    ~m1_setfam_1(u1_pre_topc(sK2),u1_struct_0(sK2)) | spl7_7),
% 0.21/0.58    inference(avatar_component_clause,[],[f299])).
% 0.21/0.58  fof(f299,plain,(
% 0.21/0.58    spl7_7 <=> m1_setfam_1(u1_pre_topc(sK2),u1_struct_0(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.58  fof(f1413,plain,(
% 0.21/0.58    spl7_7 | spl7_11),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1388])).
% 0.21/0.58  fof(f1388,plain,(
% 0.21/0.58    $false | (spl7_7 | spl7_11)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f369,f315,f1379])).
% 0.21/0.58  fof(f369,plain,(
% 0.21/0.58    ~v1_xboole_0(k1_zfmisc_1(k3_tarski(u1_pre_topc(sK2)))) | spl7_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f368])).
% 0.21/0.58  fof(f306,plain,(
% 0.21/0.58    ~spl7_7 | spl7_8),
% 0.21/0.58    inference(avatar_split_clause,[],[f297,f303,f299])).
% 0.21/0.58  fof(f297,plain,(
% 0.21/0.58    u1_struct_0(sK2) = k3_tarski(u1_pre_topc(sK2)) | ~m1_setfam_1(u1_pre_topc(sK2),u1_struct_0(sK2))),
% 0.21/0.58    inference(forward_demodulation,[],[f296,f227])).
% 0.21/0.58  fof(f227,plain,(
% 0.21/0.58    k3_tarski(u1_pre_topc(sK2)) = k5_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f105,f84])).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k3_tarski(X1) = k5_setfam_1(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.58    inference(ennf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f53,f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.58  fof(f296,plain,(
% 0.21/0.58    ~m1_setfam_1(u1_pre_topc(sK2),u1_struct_0(sK2)) | u1_struct_0(sK2) = k5_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.58    inference(resolution,[],[f85,f105])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ! [X0,X1] : (((m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) != X0) & (k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.58    inference(nnf_transformation,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0,X1] : ((m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (9314)------------------------------
% 0.21/0.58  % (9314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9314)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (9314)Memory used [KB]: 11513
% 0.21/0.58  % (9314)Time elapsed: 0.157 s
% 0.21/0.58  % (9314)------------------------------
% 0.21/0.58  % (9314)------------------------------
% 0.21/0.59  % (9299)Success in time 0.223 s
%------------------------------------------------------------------------------
