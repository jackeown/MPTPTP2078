%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 375 expanded)
%              Number of leaves         :   41 ( 159 expanded)
%              Depth                    :   11
%              Number of atoms          :  718 (1987 expanded)
%              Number of equality atoms :   80 ( 256 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f539,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f94,f102,f126,f163,f176,f181,f186,f209,f234,f240,f264,f268,f284,f285,f342,f365,f385,f396,f405,f411,f472,f505,f517,f535,f538])).

fof(f538,plain,
    ( spl7_41
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f537,f87,f82,f77,f362])).

fof(f362,plain,
    ( spl7_41
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f77,plain,
    ( spl7_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f82,plain,
    ( spl7_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f87,plain,
    ( spl7_4
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f537,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f536,f79])).

fof(f79,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f536,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f388,f84])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f388,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f88,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f88,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f535,plain,
    ( spl7_44
    | ~ spl7_60 ),
    inference(avatar_contradiction_clause,[],[f534])).

fof(f534,plain,
    ( $false
    | spl7_44
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f533,f404])).

fof(f404,plain,
    ( k1_xboole_0 != sK2
    | spl7_44 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl7_44
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f533,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f524,f95])).

fof(f95,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f57,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f524,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_60 ),
    inference(resolution,[],[f516,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f516,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f514])).

fof(f514,plain,
    ( spl7_60
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f517,plain,
    ( spl7_60
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_41
    | ~ spl7_59 ),
    inference(avatar_split_clause,[],[f512,f503,f362,f91,f82,f514])).

fof(f91,plain,
    ( spl7_5
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f503,plain,
    ( spl7_59
  <=> ! [X1] :
        ( r1_tarski(sK2,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f512,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_41
    | ~ spl7_59 ),
    inference(forward_demodulation,[],[f511,f364])).

fof(f364,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f362])).

fof(f511,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_59 ),
    inference(subsumption_resolution,[],[f508,f84])).

fof(f508,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ spl7_5
    | ~ spl7_59 ),
    inference(resolution,[],[f504,f93])).

fof(f93,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f504,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK2,k1_tops_1(sK0,X1)) )
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f503])).

fof(f505,plain,
    ( spl7_59
    | ~ spl7_27
    | ~ spl7_45
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f488,f469,f408,f262,f503])).

fof(f262,plain,
    ( spl7_27
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f408,plain,
    ( spl7_45
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f469,plain,
    ( spl7_55
  <=> sK2 = k1_tops_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f488,plain,
    ( ! [X1] :
        ( r1_tarski(sK2,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X1) )
    | ~ spl7_27
    | ~ spl7_45
    | ~ spl7_55 ),
    inference(forward_demodulation,[],[f415,f471])).

fof(f471,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f469])).

fof(f415,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X1)
        | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X1)) )
    | ~ spl7_27
    | ~ spl7_45 ),
    inference(resolution,[],[f410,f263])).

fof(f263,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f262])).

fof(f410,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f408])).

fof(f472,plain,
    ( spl7_55
    | ~ spl7_25
    | ~ spl7_43
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f466,f408,f393,f232,f469])).

fof(f232,plain,
    ( spl7_25
  <=> ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f393,plain,
    ( spl7_43
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f466,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl7_25
    | ~ spl7_43
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f397,f410])).

fof(f397,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k1_tops_1(sK0,sK2)
    | ~ spl7_25
    | ~ spl7_43 ),
    inference(resolution,[],[f395,f233])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = X0 )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f232])).

fof(f395,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f393])).

fof(f411,plain,
    ( spl7_45
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f406,f87,f408])).

fof(f406,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f42,f88])).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f32,plain,
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f405,plain,
    ( ~ spl7_44
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f400,f87,f402])).

fof(f400,plain,
    ( k1_xboole_0 != sK2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f45,f88])).

fof(f45,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f396,plain,
    ( spl7_43
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f391,f87,f393])).

fof(f391,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f44,f88])).

fof(f44,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f385,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_41 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f383,f79])).

fof(f383,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_3
    | spl7_4
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f382,f84])).

fof(f382,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl7_4
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f379,f89])).

fof(f89,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f379,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_41 ),
    inference(trivial_inequality_removal,[],[f378])).

fof(f378,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_41 ),
    inference(superposition,[],[f49,f364])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f365,plain,
    ( spl7_41
    | ~ spl7_3
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f354,f340,f281,f183,f82,f362])).

fof(f183,plain,
    ( spl7_20
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f281,plain,
    ( spl7_30
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f340,plain,
    ( spl7_40
  <=> ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f354,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl7_3
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f353,f283])).

fof(f283,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f281])).

fof(f353,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_3
    | ~ spl7_20
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f351,f185])).

fof(f185,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f183])).

fof(f351,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_3
    | ~ spl7_40 ),
    inference(resolution,[],[f341,f84])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | ~ r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f340])).

fof(f342,plain,
    ( spl7_40
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f288,f277,f340])).

fof(f277,plain,
    ( spl7_29
  <=> ! [X0] :
        ( k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl7_29 ),
    inference(resolution,[],[f278,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f277])).

fof(f285,plain,
    ( spl7_29
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f249,f207,f77,f72,f277])).

fof(f72,plain,
    ( spl7_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f207,plain,
    ( spl7_23
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f248,f74])).

fof(f74,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_2
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f246,f79])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_23 ),
    inference(resolution,[],[f53,f208])).

fof(f208,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK0)
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f207])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f284,plain,
    ( spl7_30
    | ~ spl7_6
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f275,f266,f99,f281])).

fof(f99,plain,
    ( spl7_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f266,plain,
    ( spl7_28
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f275,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_6
    | ~ spl7_28 ),
    inference(resolution,[],[f267,f101])).

fof(f101,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f266])).

fof(f268,plain,
    ( spl7_28
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f193,f183,f266])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl7_20 ),
    inference(resolution,[],[f185,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f264,plain,
    ( spl7_27
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f225,f77,f262])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f50,f79])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f240,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f237,f74])).

fof(f237,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(resolution,[],[f180,f79])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl7_19
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f234,plain,
    ( spl7_25
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f192,f174,f77,f232])).

fof(f174,plain,
    ( spl7_18
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = X0 )
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(resolution,[],[f175,f79])).

fof(f175,plain,
    ( ! [X3,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_tops_1(X1,X3) = X3 )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f209,plain,
    ( spl7_23
    | spl7_4 ),
    inference(avatar_split_clause,[],[f201,f87,f207])).

fof(f201,plain,
    ( ! [X3] :
        ( k1_xboole_0 = X3
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_4 ),
    inference(subsumption_resolution,[],[f41,f89])).

fof(f41,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f186,plain,
    ( spl7_20
    | ~ spl7_3
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f165,f161,f82,f183])).

fof(f161,plain,
    ( spl7_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f165,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl7_3
    | ~ spl7_16 ),
    inference(resolution,[],[f162,f84])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f181,plain,
    ( spl7_19
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f177,f124,f179])).

fof(f124,plain,
    ( spl7_11
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ sP5(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f125,f111])).

fof(f111,plain,(
    ! [X0] : sP5(X0) ),
    inference(resolution,[],[f67,f46])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP5(X0) ) ),
    inference(cnf_transformation,[],[f67_D])).

fof(f67_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    <=> ~ sP5(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ sP5(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f176,plain,
    ( spl7_18
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f167,f120,f174])).

fof(f120,plain,
    ( spl7_10
  <=> sP6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f167,plain,
    ( ! [X3,X1] :
        ( k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f70,f122])).

fof(f122,plain,
    ( sP6
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f70,plain,(
    ! [X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sP6 ) ),
    inference(general_splitting,[],[f68,f69_D])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP5(X0)
      | sP6 ) ),
    inference(cnf_transformation,[],[f69_D])).

fof(f69_D,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ sP5(X0) )
  <=> ~ sP6 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP5(X0) ) ),
    inference(general_splitting,[],[f51,f67_D])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f163,plain,
    ( spl7_16
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f149,f77,f161])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f47,f79])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f126,plain,
    ( spl7_10
    | spl7_11 ),
    inference(avatar_split_clause,[],[f69,f124,f120])).

fof(f102,plain,
    ( spl7_6
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f96,f82,f99])).

fof(f96,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl7_3 ),
    inference(resolution,[],[f57,f84])).

fof(f94,plain,
    ( ~ spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f43,f91,f87])).

fof(f43,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f38,f72])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (23656)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (23655)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (23656)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (23658)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (23660)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (23676)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % (23675)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (23659)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (23664)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (23657)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (23678)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.49  % (23667)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (23669)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (23666)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (23672)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (23665)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (23659)Refutation not found, incomplete strategy% (23659)------------------------------
% 0.20/0.50  % (23659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23659)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (23659)Memory used [KB]: 6140
% 0.20/0.50  % (23659)Time elapsed: 0.066 s
% 0.20/0.50  % (23659)------------------------------
% 0.20/0.50  % (23659)------------------------------
% 0.20/0.50  % (23677)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f539,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f75,f80,f85,f94,f102,f126,f163,f176,f181,f186,f209,f234,f240,f264,f268,f284,f285,f342,f365,f385,f396,f405,f411,f472,f505,f517,f535,f538])).
% 0.20/0.51  fof(f538,plain,(
% 0.20/0.51    spl7_41 | ~spl7_2 | ~spl7_3 | ~spl7_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f537,f87,f82,f77,f362])).
% 0.20/0.51  fof(f362,plain,(
% 0.20/0.51    spl7_41 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    spl7_2 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl7_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    spl7_4 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.51  fof(f537,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f536,f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    l1_pre_topc(sK0) | ~spl7_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f77])).
% 0.20/0.51  fof(f536,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl7_3 | ~spl7_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f388,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f388,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl7_4),
% 0.20/0.51    inference(resolution,[],[f88,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    v2_tops_1(sK1,sK0) | ~spl7_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f87])).
% 0.20/0.51  fof(f535,plain,(
% 0.20/0.51    spl7_44 | ~spl7_60),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f534])).
% 0.20/0.51  fof(f534,plain,(
% 0.20/0.51    $false | (spl7_44 | ~spl7_60)),
% 0.20/0.51    inference(subsumption_resolution,[],[f533,f404])).
% 0.20/0.51  fof(f404,plain,(
% 0.20/0.51    k1_xboole_0 != sK2 | spl7_44),
% 0.20/0.51    inference(avatar_component_clause,[],[f402])).
% 0.20/0.51  fof(f402,plain,(
% 0.20/0.51    spl7_44 <=> k1_xboole_0 = sK2),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.20/0.51  fof(f533,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | ~spl7_60),
% 0.20/0.51    inference(subsumption_resolution,[],[f524,f95])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f57,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f524,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2 | ~spl7_60),
% 0.20/0.51    inference(resolution,[],[f516,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f516,plain,(
% 0.20/0.51    r1_tarski(sK2,k1_xboole_0) | ~spl7_60),
% 0.20/0.51    inference(avatar_component_clause,[],[f514])).
% 0.20/0.51  fof(f514,plain,(
% 0.20/0.51    spl7_60 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 0.20/0.51  fof(f517,plain,(
% 0.20/0.51    spl7_60 | ~spl7_3 | ~spl7_5 | ~spl7_41 | ~spl7_59),
% 0.20/0.51    inference(avatar_split_clause,[],[f512,f503,f362,f91,f82,f514])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl7_5 <=> r1_tarski(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.51  fof(f503,plain,(
% 0.20/0.51    spl7_59 <=> ! [X1] : (r1_tarski(sK2,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 0.20/0.51  fof(f512,plain,(
% 0.20/0.51    r1_tarski(sK2,k1_xboole_0) | (~spl7_3 | ~spl7_5 | ~spl7_41 | ~spl7_59)),
% 0.20/0.51    inference(forward_demodulation,[],[f511,f364])).
% 0.20/0.51  fof(f364,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl7_41),
% 0.20/0.51    inference(avatar_component_clause,[],[f362])).
% 0.20/0.51  fof(f511,plain,(
% 0.20/0.51    r1_tarski(sK2,k1_tops_1(sK0,sK1)) | (~spl7_3 | ~spl7_5 | ~spl7_59)),
% 0.20/0.51    inference(subsumption_resolution,[],[f508,f84])).
% 0.20/0.51  fof(f508,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,k1_tops_1(sK0,sK1)) | (~spl7_5 | ~spl7_59)),
% 0.20/0.51    inference(resolution,[],[f504,f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    r1_tarski(sK2,sK1) | ~spl7_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f91])).
% 0.20/0.51  fof(f504,plain,(
% 0.20/0.51    ( ! [X1] : (~r1_tarski(sK2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,k1_tops_1(sK0,X1))) ) | ~spl7_59),
% 0.20/0.51    inference(avatar_component_clause,[],[f503])).
% 0.20/0.51  fof(f505,plain,(
% 0.20/0.51    spl7_59 | ~spl7_27 | ~spl7_45 | ~spl7_55),
% 0.20/0.51    inference(avatar_split_clause,[],[f488,f469,f408,f262,f503])).
% 0.20/0.51  fof(f262,plain,(
% 0.20/0.51    spl7_27 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.20/0.51  fof(f408,plain,(
% 0.20/0.51    spl7_45 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.20/0.51  fof(f469,plain,(
% 0.20/0.51    spl7_55 <=> sK2 = k1_tops_1(sK0,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 0.20/0.51  fof(f488,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(sK2,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X1)) ) | (~spl7_27 | ~spl7_45 | ~spl7_55)),
% 0.20/0.51    inference(forward_demodulation,[],[f415,f471])).
% 0.20/0.51  fof(f471,plain,(
% 0.20/0.51    sK2 = k1_tops_1(sK0,sK2) | ~spl7_55),
% 0.20/0.51    inference(avatar_component_clause,[],[f469])).
% 0.20/0.51  fof(f415,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X1) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X1))) ) | (~spl7_27 | ~spl7_45)),
% 0.20/0.51    inference(resolution,[],[f410,f263])).
% 0.20/0.51  fof(f263,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))) ) | ~spl7_27),
% 0.20/0.51    inference(avatar_component_clause,[],[f262])).
% 0.20/0.51  fof(f410,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_45),
% 0.20/0.51    inference(avatar_component_clause,[],[f408])).
% 0.20/0.51  fof(f472,plain,(
% 0.20/0.51    spl7_55 | ~spl7_25 | ~spl7_43 | ~spl7_45),
% 0.20/0.51    inference(avatar_split_clause,[],[f466,f408,f393,f232,f469])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    spl7_25 <=> ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.20/0.51  fof(f393,plain,(
% 0.20/0.51    spl7_43 <=> v3_pre_topc(sK2,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.20/0.51  fof(f466,plain,(
% 0.20/0.51    sK2 = k1_tops_1(sK0,sK2) | (~spl7_25 | ~spl7_43 | ~spl7_45)),
% 0.20/0.51    inference(subsumption_resolution,[],[f397,f410])).
% 0.20/0.51  fof(f397,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k1_tops_1(sK0,sK2) | (~spl7_25 | ~spl7_43)),
% 0.20/0.51    inference(resolution,[],[f395,f233])).
% 0.20/0.51  fof(f233,plain,(
% 0.20/0.51    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = X0) ) | ~spl7_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f232])).
% 0.20/0.51  fof(f395,plain,(
% 0.20/0.51    v3_pre_topc(sK2,sK0) | ~spl7_43),
% 0.20/0.51    inference(avatar_component_clause,[],[f393])).
% 0.20/0.51  fof(f411,plain,(
% 0.20/0.51    spl7_45 | ~spl7_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f406,f87,f408])).
% 0.20/0.51  fof(f406,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_4),
% 0.20/0.51    inference(subsumption_resolution,[],[f42,f88])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(rectify,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f11])).
% 0.20/0.51  fof(f11,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.20/0.51  fof(f405,plain,(
% 0.20/0.51    ~spl7_44 | ~spl7_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f400,f87,f402])).
% 0.20/0.51  fof(f400,plain,(
% 0.20/0.51    k1_xboole_0 != sK2 | ~spl7_4),
% 0.20/0.51    inference(subsumption_resolution,[],[f45,f88])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f396,plain,(
% 0.20/0.51    spl7_43 | ~spl7_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f391,f87,f393])).
% 0.20/0.51  fof(f391,plain,(
% 0.20/0.51    v3_pre_topc(sK2,sK0) | ~spl7_4),
% 0.20/0.51    inference(subsumption_resolution,[],[f44,f88])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f385,plain,(
% 0.20/0.51    ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_41),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f384])).
% 0.20/0.51  fof(f384,plain,(
% 0.20/0.51    $false | (~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_41)),
% 0.20/0.51    inference(subsumption_resolution,[],[f383,f79])).
% 0.20/0.51  fof(f383,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | (~spl7_3 | spl7_4 | ~spl7_41)),
% 0.20/0.51    inference(subsumption_resolution,[],[f382,f84])).
% 0.20/0.51  fof(f382,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl7_4 | ~spl7_41)),
% 0.20/0.51    inference(subsumption_resolution,[],[f379,f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ~v2_tops_1(sK1,sK0) | spl7_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f87])).
% 0.20/0.51  fof(f379,plain,(
% 0.20/0.51    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl7_41),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f378])).
% 0.20/0.51  fof(f378,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl7_41),
% 0.20/0.51    inference(superposition,[],[f49,f364])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f365,plain,(
% 0.20/0.51    spl7_41 | ~spl7_3 | ~spl7_20 | ~spl7_30 | ~spl7_40),
% 0.20/0.51    inference(avatar_split_clause,[],[f354,f340,f281,f183,f82,f362])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    spl7_20 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.51  fof(f281,plain,(
% 0.20/0.51    spl7_30 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.20/0.51  fof(f340,plain,(
% 0.20/0.51    spl7_40 <=> ! [X0] : (~r1_tarski(k1_tops_1(sK0,X0),sK1) | k1_xboole_0 = k1_tops_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.20/0.51  fof(f354,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl7_3 | ~spl7_20 | ~spl7_30 | ~spl7_40)),
% 0.20/0.51    inference(subsumption_resolution,[],[f353,f283])).
% 0.20/0.51  fof(f283,plain,(
% 0.20/0.51    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl7_30),
% 0.20/0.51    inference(avatar_component_clause,[],[f281])).
% 0.20/0.51  fof(f353,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl7_3 | ~spl7_20 | ~spl7_40)),
% 0.20/0.51    inference(subsumption_resolution,[],[f351,f185])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl7_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f183])).
% 0.20/0.51  fof(f351,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl7_3 | ~spl7_40)),
% 0.20/0.51    inference(resolution,[],[f341,f84])).
% 0.20/0.51  fof(f341,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0))) ) | ~spl7_40),
% 0.20/0.51    inference(avatar_component_clause,[],[f340])).
% 0.20/0.51  fof(f342,plain,(
% 0.20/0.51    spl7_40 | ~spl7_29),
% 0.20/0.51    inference(avatar_split_clause,[],[f288,f277,f340])).
% 0.20/0.51  fof(f277,plain,(
% 0.20/0.51    spl7_29 <=> ! [X0] : (k1_xboole_0 = k1_tops_1(sK0,X0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,X0),sK1) | k1_xboole_0 = k1_tops_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0))) ) | ~spl7_29),
% 0.20/0.51    inference(resolution,[],[f278,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f37])).
% 0.20/0.51  fof(f278,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | k1_xboole_0 = k1_tops_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_29),
% 0.20/0.51    inference(avatar_component_clause,[],[f277])).
% 0.20/0.51  fof(f285,plain,(
% 0.20/0.51    spl7_29 | ~spl7_1 | ~spl7_2 | ~spl7_23),
% 0.20/0.51    inference(avatar_split_clause,[],[f249,f207,f77,f72,f277])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl7_1 <=> v2_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    spl7_23 <=> ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.51  fof(f249,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_1 | ~spl7_2 | ~spl7_23)),
% 0.20/0.51    inference(subsumption_resolution,[],[f248,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    v2_pre_topc(sK0) | ~spl7_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f72])).
% 0.20/0.51  fof(f248,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,X0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_2 | ~spl7_23)),
% 0.20/0.51    inference(subsumption_resolution,[],[f246,f79])).
% 0.20/0.51  fof(f246,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,X0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_23),
% 0.20/0.51    inference(resolution,[],[f53,f208])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    ( ! [X3] : (~v3_pre_topc(X3,sK0) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_23),
% 0.20/0.51    inference(avatar_component_clause,[],[f207])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.51  fof(f284,plain,(
% 0.20/0.51    spl7_30 | ~spl7_6 | ~spl7_28),
% 0.20/0.51    inference(avatar_split_clause,[],[f275,f266,f99,f281])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    spl7_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.51  fof(f266,plain,(
% 0.20/0.51    spl7_28 <=> ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.20/0.51  fof(f275,plain,(
% 0.20/0.51    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl7_6 | ~spl7_28)),
% 0.20/0.51    inference(resolution,[],[f267,f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl7_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f99])).
% 0.20/0.51  fof(f267,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | ~spl7_28),
% 0.20/0.51    inference(avatar_component_clause,[],[f266])).
% 0.20/0.51  fof(f268,plain,(
% 0.20/0.51    spl7_28 | ~spl7_20),
% 0.20/0.51    inference(avatar_split_clause,[],[f193,f183,f266])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | ~spl7_20),
% 0.20/0.51    inference(resolution,[],[f185,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.51  fof(f264,plain,(
% 0.20/0.51    spl7_27 | ~spl7_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f225,f77,f262])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))) ) | ~spl7_2),
% 0.20/0.51    inference(resolution,[],[f50,f79])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.20/0.51  fof(f240,plain,(
% 0.20/0.51    ~spl7_1 | ~spl7_2 | ~spl7_19),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f239])).
% 0.20/0.51  fof(f239,plain,(
% 0.20/0.51    $false | (~spl7_1 | ~spl7_2 | ~spl7_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f237,f74])).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    ~v2_pre_topc(sK0) | (~spl7_2 | ~spl7_19)),
% 0.20/0.51    inference(resolution,[],[f180,f79])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl7_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f179])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    spl7_19 <=> ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.51  fof(f234,plain,(
% 0.20/0.51    spl7_25 | ~spl7_2 | ~spl7_18),
% 0.20/0.51    inference(avatar_split_clause,[],[f192,f174,f77,f232])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    spl7_18 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = X0) ) | (~spl7_2 | ~spl7_18)),
% 0.20/0.51    inference(resolution,[],[f175,f79])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    ( ! [X3,X1] : (~l1_pre_topc(X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X1,X3) = X3) ) | ~spl7_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f174])).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    spl7_23 | spl7_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f201,f87,f207])).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | spl7_4),
% 0.20/0.51    inference(subsumption_resolution,[],[f41,f89])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    spl7_20 | ~spl7_3 | ~spl7_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f165,f161,f82,f183])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    spl7_16 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl7_3 | ~spl7_16)),
% 0.20/0.51    inference(resolution,[],[f162,f84])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | ~spl7_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f161])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    spl7_19 | ~spl7_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f177,f124,f179])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    spl7_11 <=> ! [X0] : (~l1_pre_topc(X0) | ~sP5(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl7_11),
% 0.20/0.51    inference(subsumption_resolution,[],[f125,f111])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X0] : (sP5(X0)) )),
% 0.20/0.51    inference(resolution,[],[f67,f46])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP5(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f67_D])).
% 0.20/0.51  fof(f67_D,plain,(
% 0.20/0.51    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) <=> ~sP5(X0)) )),
% 0.20/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | ~sP5(X0) | ~v2_pre_topc(X0)) ) | ~spl7_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f124])).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    spl7_18 | ~spl7_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f167,f120,f174])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    spl7_10 <=> sP6),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    ( ! [X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl7_10),
% 0.20/0.51    inference(subsumption_resolution,[],[f70,f122])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    sP6 | ~spl7_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f120])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sP6) )),
% 0.20/0.51    inference(general_splitting,[],[f68,f69_D])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP5(X0) | sP6) )),
% 0.20/0.51    inference(cnf_transformation,[],[f69_D])).
% 0.20/0.51  fof(f69_D,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP5(X0)) ) <=> ~sP6),
% 0.20/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP5(X0)) )),
% 0.20/0.51    inference(general_splitting,[],[f51,f67_D])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    spl7_16 | ~spl7_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f149,f77,f161])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | ~spl7_2),
% 0.20/0.51    inference(resolution,[],[f47,f79])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    spl7_10 | spl7_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f69,f124,f120])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    spl7_6 | ~spl7_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f96,f82,f99])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl7_3),
% 0.20/0.51    inference(resolution,[],[f57,f84])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ~spl7_4 | spl7_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f43,f91,f87])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl7_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f40,f82])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    spl7_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f39,f77])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    spl7_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f72])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (23656)------------------------------
% 0.20/0.51  % (23656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23656)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (23656)Memory used [KB]: 6396
% 0.20/0.51  % (23656)Time elapsed: 0.089 s
% 0.20/0.51  % (23656)------------------------------
% 0.20/0.51  % (23656)------------------------------
% 0.20/0.51  % (23673)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (23651)Success in time 0.154 s
%------------------------------------------------------------------------------
