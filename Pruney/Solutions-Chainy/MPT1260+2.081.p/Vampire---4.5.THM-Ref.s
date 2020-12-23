%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:46 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 501 expanded)
%              Number of leaves         :   33 ( 155 expanded)
%              Depth                    :   17
%              Number of atoms          :  453 (2144 expanded)
%              Number of equality atoms :   91 ( 551 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f870,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f106,f113,f133,f140,f608,f610,f612,f615,f617,f821,f829,f836,f842,f859])).

fof(f859,plain,(
    ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f856])).

fof(f856,plain,
    ( $false
    | ~ spl3_23 ),
    inference(resolution,[],[f841,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f841,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f840])).

fof(f840,plain,
    ( spl3_23
  <=> ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f842,plain,
    ( ~ spl3_16
    | spl3_23
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f838,f816,f840,f601])).

fof(f601,plain,
    ( spl3_16
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f816,plain,
    ( spl3_20
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f838,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_20 ),
    inference(resolution,[],[f817,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f817,plain,
    ( ! [X2,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f816])).

fof(f836,plain,
    ( spl3_2
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f835])).

fof(f835,plain,
    ( $false
    | spl3_2
    | ~ spl3_22 ),
    inference(trivial_inequality_removal,[],[f834])).

fof(f834,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | spl3_2
    | ~ spl3_22 ),
    inference(superposition,[],[f76,f830])).

fof(f830,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f683,f828])).

fof(f828,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f826])).

fof(f826,plain,
    ( spl3_22
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f683,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f669,f47])).

fof(f669,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f52,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f76,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f829,plain,
    ( spl3_22
    | ~ spl3_17
    | ~ spl3_1
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f824,f819,f71,f605,f826])).

fof(f605,plain,
    ( spl3_17
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f71,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f819,plain,
    ( spl3_21
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f824,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_21 ),
    inference(resolution,[],[f822,f73])).

fof(f73,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f822,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = X0 )
    | ~ spl3_21 ),
    inference(resolution,[],[f820,f46])).

fof(f820,plain,
    ( ! [X3,X1] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f819])).

fof(f821,plain,
    ( spl3_20
    | spl3_21 ),
    inference(avatar_split_clause,[],[f53,f819,f816])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f617,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f73,f80])).

fof(f80,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f49,f77])).

fof(f77,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f49,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f615,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | spl3_17 ),
    inference(resolution,[],[f607,f47])).

fof(f607,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f605])).

fof(f612,plain,(
    spl3_16 ),
    inference(avatar_contradiction_clause,[],[f611])).

fof(f611,plain,
    ( $false
    | spl3_16 ),
    inference(resolution,[],[f603,f46])).

fof(f603,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f601])).

fof(f610,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | spl3_15 ),
    inference(resolution,[],[f599,f45])).

fof(f599,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl3_15
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f608,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f595,f130,f103,f99,f75,f71,f605,f601,f597])).

fof(f99,plain,
    ( spl3_3
  <=> m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f103,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f130,plain,
    ( spl3_6
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f595,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f62,f594])).

fof(f594,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f348,f592])).

fof(f592,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f591,f84])).

fof(f84,plain,(
    ! [X8,X7] : k9_subset_1(X7,X8,X8) = X8 ),
    inference(resolution,[],[f65,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f4,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f591,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f588,f181])).

fof(f181,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f95,f176])).

fof(f176,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f173,f77])).

fof(f173,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f167,f157])).

fof(f157,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl3_4 ),
    inference(resolution,[],[f68,f105])).

fof(f105,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f167,plain,
    ( ! [X10] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X10) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X10)))
    | ~ spl3_6 ),
    inference(resolution,[],[f69,f132])).

fof(f132,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f95,plain,(
    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(resolution,[],[f92,f47])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X0)) = X0 ) ),
    inference(resolution,[],[f91,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f60,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f91,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f50,f46])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f588,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f517,f180])).

fof(f180,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f100,f176])).

fof(f100,plain,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f517,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X18)) = k7_subset_1(u1_struct_0(sK0),sK1,X18) )
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f515,f171])).

fof(f171,plain,
    ( ! [X12] : k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X12) = k7_subset_1(u1_struct_0(sK0),sK1,X12)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f169,f168])).

fof(f168,plain,(
    ! [X11] : k7_subset_1(u1_struct_0(sK0),sK1,X11) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X11))) ),
    inference(resolution,[],[f69,f47])).

fof(f169,plain,
    ( ! [X12] : k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X12) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X12)))
    | ~ spl3_4 ),
    inference(resolution,[],[f69,f105])).

fof(f515,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X18) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X18)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f61,f105])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f348,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f307,f47])).

fof(f307,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f51,f46])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f140,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f136,f47])).

fof(f136,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(resolution,[],[f134,f116])).

fof(f116,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f134,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(resolution,[],[f128,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f128,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_5
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f133,plain,
    ( ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f124,f130,f126])).

fof(f124,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f58,f122])).

fof(f122,plain,(
    k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f118,f47])).

fof(f118,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1))) ) ),
    inference(resolution,[],[f116,f60])).

fof(f113,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f110,f47])).

fof(f110,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_3 ),
    inference(resolution,[],[f109,f91])).

fof(f109,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_3 ),
    inference(resolution,[],[f107,f64])).

fof(f107,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_3 ),
    inference(resolution,[],[f101,f58])).

fof(f101,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f106,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f97,f103,f99])).

fof(f97,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(superposition,[],[f58,f95])).

fof(f78,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f48,f75,f71])).

fof(f48,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:48:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (8381)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.47  % (8375)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.47  % (8377)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.49  % (8385)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.49  % (8389)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.49  % (8378)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.50  % (8376)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.50  % (8380)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.50  % (8379)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.50  % (8392)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.51  % (8388)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.51  % (8377)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f870,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(avatar_sat_refutation,[],[f78,f106,f113,f133,f140,f608,f610,f612,f615,f617,f821,f829,f836,f842,f859])).
% 0.23/0.51  fof(f859,plain,(
% 0.23/0.51    ~spl3_23),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f856])).
% 0.23/0.51  fof(f856,plain,(
% 0.23/0.51    $false | ~spl3_23),
% 0.23/0.51    inference(resolution,[],[f841,f47])).
% 0.23/0.51  fof(f47,plain,(
% 0.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.51    inference(cnf_transformation,[],[f42])).
% 0.23/0.51  fof(f42,plain,(
% 0.23/0.51    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 0.23/0.51  fof(f40,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f41,plain,(
% 0.23/0.51    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f38])).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.51    inference(nnf_transformation,[],[f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f18])).
% 0.23/0.51  fof(f18,negated_conjecture,(
% 0.23/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.23/0.51    inference(negated_conjecture,[],[f17])).
% 0.23/0.51  fof(f17,conjecture,(
% 0.23/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 0.23/0.51  fof(f841,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_23),
% 0.23/0.51    inference(avatar_component_clause,[],[f840])).
% 0.23/0.51  fof(f840,plain,(
% 0.23/0.51    spl3_23 <=> ! [X0] : ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.23/0.51  fof(f842,plain,(
% 0.23/0.51    ~spl3_16 | spl3_23 | ~spl3_20),
% 0.23/0.51    inference(avatar_split_clause,[],[f838,f816,f840,f601])).
% 0.23/0.51  fof(f601,plain,(
% 0.23/0.51    spl3_16 <=> l1_pre_topc(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.23/0.51  fof(f816,plain,(
% 0.23/0.51    spl3_20 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.23/0.51  fof(f838,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_20),
% 0.23/0.51    inference(resolution,[],[f817,f45])).
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    v2_pre_topc(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f42])).
% 0.23/0.51  fof(f817,plain,(
% 0.23/0.51    ( ! [X2,X0] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_20),
% 0.23/0.51    inference(avatar_component_clause,[],[f816])).
% 0.23/0.51  fof(f836,plain,(
% 0.23/0.51    spl3_2 | ~spl3_22),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f835])).
% 0.23/0.51  fof(f835,plain,(
% 0.23/0.51    $false | (spl3_2 | ~spl3_22)),
% 0.23/0.51    inference(trivial_inequality_removal,[],[f834])).
% 0.23/0.51  fof(f834,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | (spl3_2 | ~spl3_22)),
% 0.23/0.51    inference(superposition,[],[f76,f830])).
% 0.23/0.51  fof(f830,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_22),
% 0.23/0.51    inference(backward_demodulation,[],[f683,f828])).
% 0.23/0.51  fof(f828,plain,(
% 0.23/0.51    sK1 = k1_tops_1(sK0,sK1) | ~spl3_22),
% 0.23/0.51    inference(avatar_component_clause,[],[f826])).
% 0.23/0.51  fof(f826,plain,(
% 0.23/0.51    spl3_22 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.23/0.51  fof(f683,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.23/0.51    inference(resolution,[],[f669,f47])).
% 0.23/0.51  fof(f669,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 0.23/0.51    inference(resolution,[],[f52,f46])).
% 0.23/0.51  fof(f46,plain,(
% 0.23/0.51    l1_pre_topc(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f42])).
% 0.23/0.51  fof(f52,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f24])).
% 0.23/0.51  fof(f24,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f14])).
% 0.23/0.51  fof(f14,axiom,(
% 0.23/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.23/0.51  fof(f76,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 0.23/0.51    inference(avatar_component_clause,[],[f75])).
% 0.23/0.51  fof(f75,plain,(
% 0.23/0.51    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.51  fof(f829,plain,(
% 0.23/0.51    spl3_22 | ~spl3_17 | ~spl3_1 | ~spl3_21),
% 0.23/0.51    inference(avatar_split_clause,[],[f824,f819,f71,f605,f826])).
% 0.23/0.51  fof(f605,plain,(
% 0.23/0.51    spl3_17 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.23/0.51  fof(f71,plain,(
% 0.23/0.51    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.51  fof(f819,plain,(
% 0.23/0.51    spl3_21 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.23/0.51  fof(f824,plain,(
% 0.23/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,sK1) | (~spl3_1 | ~spl3_21)),
% 0.23/0.51    inference(resolution,[],[f822,f73])).
% 0.23/0.51  fof(f73,plain,(
% 0.23/0.51    v3_pre_topc(sK1,sK0) | ~spl3_1),
% 0.23/0.51    inference(avatar_component_clause,[],[f71])).
% 0.23/0.51  fof(f822,plain,(
% 0.23/0.51    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = X0) ) | ~spl3_21),
% 0.23/0.51    inference(resolution,[],[f820,f46])).
% 0.23/0.51  fof(f820,plain,(
% 0.23/0.51    ( ! [X3,X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1)) ) | ~spl3_21),
% 0.23/0.51    inference(avatar_component_clause,[],[f819])).
% 0.23/0.51  fof(f821,plain,(
% 0.23/0.51    spl3_20 | spl3_21),
% 0.23/0.51    inference(avatar_split_clause,[],[f53,f819,f816])).
% 0.23/0.51  fof(f53,plain,(
% 0.23/0.51    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f26])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f25])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f15])).
% 0.23/0.51  fof(f15,axiom,(
% 0.23/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.23/0.51  fof(f617,plain,(
% 0.23/0.51    ~spl3_1 | ~spl3_2),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f616])).
% 0.23/0.51  fof(f616,plain,(
% 0.23/0.51    $false | (~spl3_1 | ~spl3_2)),
% 0.23/0.51    inference(resolution,[],[f73,f80])).
% 0.23/0.51  fof(f80,plain,(
% 0.23/0.51    ~v3_pre_topc(sK1,sK0) | ~spl3_2),
% 0.23/0.51    inference(trivial_inequality_removal,[],[f79])).
% 0.23/0.51  fof(f79,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~spl3_2),
% 0.23/0.51    inference(forward_demodulation,[],[f49,f77])).
% 0.23/0.51  fof(f77,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 0.23/0.51    inference(avatar_component_clause,[],[f75])).
% 0.23/0.51  fof(f49,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f42])).
% 0.23/0.51  fof(f615,plain,(
% 0.23/0.51    spl3_17),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f613])).
% 0.23/0.51  fof(f613,plain,(
% 0.23/0.51    $false | spl3_17),
% 0.23/0.51    inference(resolution,[],[f607,f47])).
% 0.23/0.51  fof(f607,plain,(
% 0.23/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_17),
% 0.23/0.51    inference(avatar_component_clause,[],[f605])).
% 0.23/0.51  fof(f612,plain,(
% 0.23/0.51    spl3_16),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f611])).
% 0.23/0.51  fof(f611,plain,(
% 0.23/0.51    $false | spl3_16),
% 0.23/0.51    inference(resolution,[],[f603,f46])).
% 0.23/0.51  fof(f603,plain,(
% 0.23/0.51    ~l1_pre_topc(sK0) | spl3_16),
% 0.23/0.51    inference(avatar_component_clause,[],[f601])).
% 0.23/0.51  fof(f610,plain,(
% 0.23/0.51    spl3_15),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f609])).
% 0.23/0.51  fof(f609,plain,(
% 0.23/0.51    $false | spl3_15),
% 0.23/0.51    inference(resolution,[],[f599,f45])).
% 0.23/0.51  fof(f599,plain,(
% 0.23/0.51    ~v2_pre_topc(sK0) | spl3_15),
% 0.23/0.51    inference(avatar_component_clause,[],[f597])).
% 0.23/0.51  fof(f597,plain,(
% 0.23/0.51    spl3_15 <=> v2_pre_topc(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.23/0.51  fof(f608,plain,(
% 0.23/0.51    ~spl3_15 | ~spl3_16 | ~spl3_17 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 0.23/0.51    inference(avatar_split_clause,[],[f595,f130,f103,f99,f75,f71,f605,f601,f597])).
% 0.23/0.51  fof(f99,plain,(
% 0.23/0.51    spl3_3 <=> m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.51  fof(f103,plain,(
% 0.23/0.51    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.51  fof(f130,plain,(
% 0.23/0.51    spl3_6 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.23/0.51  fof(f595,plain,(
% 0.23/0.51    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.23/0.51    inference(superposition,[],[f62,f594])).
% 0.23/0.51  fof(f594,plain,(
% 0.23/0.51    sK1 = k1_tops_1(sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.23/0.51    inference(backward_demodulation,[],[f348,f592])).
% 0.23/0.51  fof(f592,plain,(
% 0.23/0.51    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.23/0.51    inference(forward_demodulation,[],[f591,f84])).
% 0.23/0.51  fof(f84,plain,(
% 0.23/0.51    ( ! [X8,X7] : (k9_subset_1(X7,X8,X8) = X8) )),
% 0.23/0.51    inference(resolution,[],[f65,f55])).
% 0.23/0.51  fof(f55,plain,(
% 0.23/0.51    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f44])).
% 0.23/0.51  fof(f44,plain,(
% 0.23/0.51    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f4,f43])).
% 0.23/0.51  fof(f43,plain,(
% 0.23/0.51    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.23/0.51  fof(f65,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f36])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 0.23/0.51  fof(f591,plain,(
% 0.23/0.51    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.23/0.51    inference(forward_demodulation,[],[f588,f181])).
% 0.23/0.51  fof(f181,plain,(
% 0.23/0.51    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_6)),
% 0.23/0.51    inference(backward_demodulation,[],[f95,f176])).
% 0.23/0.51  fof(f176,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_4 | ~spl3_6)),
% 0.23/0.51    inference(forward_demodulation,[],[f173,f77])).
% 0.23/0.51  fof(f173,plain,(
% 0.23/0.51    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | (~spl3_4 | ~spl3_6)),
% 0.23/0.51    inference(superposition,[],[f167,f157])).
% 0.23/0.51  fof(f157,plain,(
% 0.23/0.51    k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1))) | ~spl3_4),
% 0.23/0.51    inference(resolution,[],[f68,f105])).
% 0.23/0.51  fof(f105,plain,(
% 0.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_4),
% 0.23/0.51    inference(avatar_component_clause,[],[f103])).
% 0.23/0.51  fof(f68,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.23/0.51    inference(definition_unfolding,[],[f59,f67])).
% 0.23/0.51  fof(f67,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.23/0.51    inference(definition_unfolding,[],[f57,f56])).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,axiom,(
% 0.23/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.51  fof(f57,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.51  fof(f59,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f28])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.23/0.51  fof(f167,plain,(
% 0.23/0.51    ( ! [X10] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X10) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X10)))) ) | ~spl3_6),
% 0.23/0.51    inference(resolution,[],[f69,f132])).
% 0.23/0.51  fof(f132,plain,(
% 0.23/0.51    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.23/0.51    inference(avatar_component_clause,[],[f130])).
% 0.23/0.51  fof(f69,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 0.23/0.51    inference(definition_unfolding,[],[f66,f67])).
% 0.23/0.51  fof(f66,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f37])).
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.23/0.51  fof(f95,plain,(
% 0.23/0.51    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),
% 0.23/0.51    inference(resolution,[],[f92,f47])).
% 0.23/0.51  fof(f92,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(k2_pre_topc(sK0,X0),k3_subset_1(k2_pre_topc(sK0,X0),X0)) = X0) )),
% 0.23/0.51    inference(resolution,[],[f91,f85])).
% 0.23/0.51  fof(f85,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.23/0.51    inference(resolution,[],[f60,f64])).
% 0.23/0.51  fof(f64,plain,(
% 0.23/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f35])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.23/0.51    inference(unused_predicate_definition_removal,[],[f10])).
% 0.23/0.51  fof(f10,axiom,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.51  fof(f60,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f29])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.23/0.51  fof(f91,plain,(
% 0.23/0.51    ( ! [X0] : (r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.23/0.51    inference(resolution,[],[f50,f46])).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f12])).
% 0.23/0.51  fof(f12,axiom,(
% 0.23/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.23/0.51  fof(f588,plain,(
% 0.23/0.51    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.23/0.51    inference(resolution,[],[f517,f180])).
% 0.23/0.51  fof(f180,plain,(
% 0.23/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.23/0.51    inference(backward_demodulation,[],[f100,f176])).
% 0.23/0.51  fof(f100,plain,(
% 0.23/0.51    m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_3),
% 0.23/0.51    inference(avatar_component_clause,[],[f99])).
% 0.23/0.51  fof(f517,plain,(
% 0.23/0.51    ( ! [X18] : (~m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X18)) = k7_subset_1(u1_struct_0(sK0),sK1,X18)) ) | ~spl3_4),
% 0.23/0.51    inference(forward_demodulation,[],[f515,f171])).
% 0.23/0.51  fof(f171,plain,(
% 0.23/0.51    ( ! [X12] : (k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X12) = k7_subset_1(u1_struct_0(sK0),sK1,X12)) ) | ~spl3_4),
% 0.23/0.51    inference(forward_demodulation,[],[f169,f168])).
% 0.23/0.51  fof(f168,plain,(
% 0.23/0.51    ( ! [X11] : (k7_subset_1(u1_struct_0(sK0),sK1,X11) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X11)))) )),
% 0.23/0.51    inference(resolution,[],[f69,f47])).
% 0.23/0.51  fof(f169,plain,(
% 0.23/0.51    ( ! [X12] : (k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X12) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X12)))) ) | ~spl3_4),
% 0.23/0.51    inference(resolution,[],[f69,f105])).
% 0.23/0.51  fof(f515,plain,(
% 0.23/0.51    ( ! [X18] : (~m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X18) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X18))) ) | ~spl3_4),
% 0.23/0.51    inference(resolution,[],[f61,f105])).
% 0.23/0.51  fof(f61,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f8])).
% 0.23/0.51  fof(f8,axiom,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.23/0.51  fof(f348,plain,(
% 0.23/0.51    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.23/0.51    inference(resolution,[],[f307,f47])).
% 0.23/0.51  fof(f307,plain,(
% 0.23/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 0.23/0.51    inference(resolution,[],[f51,f46])).
% 0.23/0.51  fof(f51,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f23])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f16])).
% 0.23/0.51  fof(f16,axiom,(
% 0.23/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.23/0.51  fof(f62,plain,(
% 0.23/0.51    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f32])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f31])).
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f13])).
% 0.23/0.51  fof(f13,axiom,(
% 0.23/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.23/0.51  fof(f140,plain,(
% 0.23/0.51    spl3_5),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f138])).
% 0.23/0.51  fof(f138,plain,(
% 0.23/0.51    $false | spl3_5),
% 0.23/0.51    inference(resolution,[],[f136,f47])).
% 0.23/0.51  fof(f136,plain,(
% 0.23/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 0.23/0.51    inference(resolution,[],[f134,f116])).
% 0.23/0.51  fof(f116,plain,(
% 0.23/0.51    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.23/0.51    inference(resolution,[],[f63,f46])).
% 0.23/0.51  fof(f63,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f34])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f33])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f11])).
% 0.23/0.51  fof(f11,axiom,(
% 0.23/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.23/0.51  fof(f134,plain,(
% 0.23/0.51    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 0.23/0.51    inference(resolution,[],[f128,f58])).
% 0.23/0.51  fof(f58,plain,(
% 0.23/0.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f27])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.23/0.51  fof(f128,plain,(
% 0.23/0.51    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 0.23/0.51    inference(avatar_component_clause,[],[f126])).
% 0.23/0.51  fof(f126,plain,(
% 0.23/0.51    spl3_5 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.51  fof(f133,plain,(
% 0.23/0.51    ~spl3_5 | spl3_6),
% 0.23/0.51    inference(avatar_split_clause,[],[f124,f130,f126])).
% 0.23/0.51  fof(f124,plain,(
% 0.23/0.51    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.51    inference(superposition,[],[f58,f122])).
% 0.23/0.51  fof(f122,plain,(
% 0.23/0.51    k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 0.23/0.51    inference(resolution,[],[f118,f47])).
% 0.23/0.51  fof(f118,plain,(
% 0.23/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1)))) )),
% 0.23/0.51    inference(resolution,[],[f116,f60])).
% 0.23/0.51  fof(f113,plain,(
% 0.23/0.51    spl3_3),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f111])).
% 0.23/0.51  fof(f111,plain,(
% 0.23/0.51    $false | spl3_3),
% 0.23/0.51    inference(resolution,[],[f110,f47])).
% 0.23/0.51  fof(f110,plain,(
% 0.23/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_3),
% 0.23/0.51    inference(resolution,[],[f109,f91])).
% 0.23/0.51  fof(f109,plain,(
% 0.23/0.51    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_3),
% 0.23/0.51    inference(resolution,[],[f107,f64])).
% 0.23/0.51  fof(f107,plain,(
% 0.23/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_3),
% 0.23/0.51    inference(resolution,[],[f101,f58])).
% 0.23/0.51  fof(f101,plain,(
% 0.23/0.51    ~m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_3),
% 0.23/0.51    inference(avatar_component_clause,[],[f99])).
% 0.23/0.51  fof(f106,plain,(
% 0.23/0.51    ~spl3_3 | spl3_4),
% 0.23/0.51    inference(avatar_split_clause,[],[f97,f103,f99])).
% 0.23/0.51  fof(f97,plain,(
% 0.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.23/0.51    inference(superposition,[],[f58,f95])).
% 0.23/0.51  fof(f78,plain,(
% 0.23/0.51    spl3_1 | spl3_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f48,f75,f71])).
% 0.23/0.51  fof(f48,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f42])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (8377)------------------------------
% 0.23/0.51  % (8377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (8377)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (8377)Memory used [KB]: 6652
% 0.23/0.51  % (8377)Time elapsed: 0.071 s
% 0.23/0.51  % (8377)------------------------------
% 0.23/0.51  % (8377)------------------------------
% 0.23/0.51  % (8374)Success in time 0.143 s
%------------------------------------------------------------------------------
