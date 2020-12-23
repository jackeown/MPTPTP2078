%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 158 expanded)
%              Number of leaves         :   20 (  77 expanded)
%              Depth                    :    7
%              Number of atoms          :  348 ( 926 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f53,f58,f63,f68,f72,f80,f85,f90,f99,f105,f108])).

fof(f108,plain,
    ( ~ spl3_8
    | ~ spl3_6
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f107,f103,f97,f55,f65])).

fof(f65,plain,
    ( spl3_8
  <=> r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f55,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f97,plain,
    ( spl3_15
  <=> ! [X0] :
        ( r2_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f103,plain,
    ( spl3_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X0,sK1)
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f107,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(resolution,[],[f104,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r2_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_16
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f101,f97,f70,f103,f55,f50,f45])).

fof(f45,plain,
    ( spl3_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f50,plain,
    ( spl3_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f70,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( ~ r2_orders_2(X0,X2,X1)
        | ~ r2_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v5_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0))
        | ~ r2_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0))
        | ~ r2_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(resolution,[],[f98,f71])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_orders_2(X0,X2,X1)
        | ~ r2_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v5_orders_2(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f99,plain,
    ( spl3_15
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f91,f88,f55,f97])).

fof(f88,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( r2_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f91,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) )
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(resolution,[],[f89,f57])).

fof(f57,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,sK2,X1)) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f90,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f86,f83,f60,f88])).

fof(f60,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f83,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
        | r2_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( r2_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,sK2,X1)) )
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(resolution,[],[f84,f62])).

fof(f62,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f84,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | spl3_12
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f81,f78,f40,f83,f50,f45,f35,f30])).

fof(f30,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,
    ( spl3_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f40,plain,
    ( spl3_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f78,plain,
    ( spl3_11
  <=> ! [X1,X3,X0,X2] :
        ( r2_orders_2(X0,X1,X2)
        | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | r2_orders_2(sK0,X0,X2)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f79,f42])).

fof(f42,plain,
    ( v4_orders_2(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f79,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v4_orders_2(X0)
        | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v5_orders_2(X0)
        | r2_orders_2(X0,X1,X2)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f25,f78])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f72,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_orders_2)).

fof(f68,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f65])).

fof(f24,plain,(
    r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( r2_hidden(X1,k3_orders_2(X0,X2,X1))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k3_orders_2(sK0,X2,X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( r2_hidden(X1,k3_orders_2(sK0,X2,X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( r2_hidden(sK1,k3_orders_2(sK0,X2,sK1))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( r2_hidden(sK1,k3_orders_2(sK0,X2,sK1))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k3_orders_2(X0,X2,X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k3_orders_2(X0,X2,X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ r2_hidden(X1,k3_orders_2(X0,X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ r2_hidden(X1,k3_orders_2(X0,X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_orders_2)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f60])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:41:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (17107)WARNING: option uwaf not known.
% 0.21/0.47  % (17113)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.47  % (17113)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f53,f58,f63,f68,f72,f80,f85,f90,f99,f105,f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ~spl3_8 | ~spl3_6 | ~spl3_15 | ~spl3_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f107,f103,f97,f55,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl3_8 <=> r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl3_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    spl3_15 <=> ! [X0] : (r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl3_16 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X0,sK1) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) | (~spl3_15 | ~spl3_16)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) | (~spl3_15 | ~spl3_16)),
% 0.21/0.47    inference(resolution,[],[f104,f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X0] : (r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0))) ) | ~spl3_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f97])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0))) ) | ~spl3_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f103])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_16 | ~spl3_9 | ~spl3_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f101,f97,f70,f103,f55,f50,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl3_4 <=> v5_orders_2(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl3_5 <=> l1_orders_2(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl3_9 <=> ! [X1,X0,X2] : (~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) | ~r2_orders_2(sK0,X0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | (~spl3_9 | ~spl3_15)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0)) | ~r2_orders_2(sK0,X0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | (~spl3_9 | ~spl3_15)),
% 0.21/0.48    inference(resolution,[],[f98,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) ) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl3_15 | ~spl3_6 | ~spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f91,f88,f55,f97])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl3_13 <=> ! [X1,X0] : (r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,sK2,X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,k3_orders_2(sK0,sK2,X0))) ) | (~spl3_6 | ~spl3_13)),
% 0.21/0.48    inference(resolution,[],[f89,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,sK2,X1))) ) | ~spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl3_13 | ~spl3_7 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f86,f83,f60,f88])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl3_12 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | r2_orders_2(sK0,X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,sK2,X1))) ) | (~spl3_7 | ~spl3_12)),
% 0.21/0.48    inference(resolution,[],[f84,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,X1,X2))) ) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | spl3_12 | ~spl3_3 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f81,f78,f40,f83,f50,f45,f35,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    spl3_1 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    spl3_2 <=> v3_orders_2(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl3_3 <=> v4_orders_2(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl3_11 <=> ! [X1,X3,X0,X2] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | r2_orders_2(sK0,X0,X2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl3_3 | ~spl3_11)),
% 0.21/0.48    inference(resolution,[],[f79,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    v4_orders_2(sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v4_orders_2(X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | r2_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) ) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f78])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f70])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r2_orders_2(X0,X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_orders_2)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f65])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ((r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k3_orders_2(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (r2_hidden(X1,k3_orders_2(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (r2_hidden(X1,k3_orders_2(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (r2_hidden(sK1,k3_orders_2(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X2] : (r2_hidden(sK1,k3_orders_2(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k3_orders_2(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f5])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k3_orders_2(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~r2_hidden(X1,k3_orders_2(X0,X2,X1)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f3])).
% 0.21/0.48  fof(f3,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~r2_hidden(X1,k3_orders_2(X0,X2,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_orders_2)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f60])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f55])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f50])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    l1_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f45])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    v5_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f40])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    v4_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f35])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    v3_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f30])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17113)------------------------------
% 0.21/0.48  % (17113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17113)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17113)Memory used [KB]: 5373
% 0.21/0.48  % (17113)Time elapsed: 0.007 s
% 0.21/0.48  % (17113)------------------------------
% 0.21/0.48  % (17113)------------------------------
% 0.21/0.48  % (17096)Success in time 0.119 s
%------------------------------------------------------------------------------
